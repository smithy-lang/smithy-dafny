package software.amazon.polymorph.smithygo.localservice;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;
import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithygo.codegen.ApplicationProtocol;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.localservice.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.localservice.shapevisitor.ShapeVisitorHelper;
import software.amazon.polymorph.smithygo.localservice.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.smithygo.utils.Constants;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public class DafnyLocalServiceTypeConversionProtocol
  implements ProtocolGenerator {

  public static final String TO_DAFNY = "to_dafny.go";
  public static final String TO_NATIVE = "to_native.go";

  @Override
  public ShapeId getProtocol() {
    return ShapeId.from("aws.polymorph#localService");
  }

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return null;
  }

  @Override
  public void generateSerializers(final GenerationContext context) {
    final Set<ShapeId> alreadyVisited = new HashSet<>();
    final var model = context.model();
    final var serviceShape = model.expectShape(
      context.settings().getService(),
      ServiceShape.class
    );
    final var symbolProvider = context.symbolProvider();
    final var writerDelegator = context.writerDelegator();
    serviceShape
      .getOperations()
      .stream()
      .sorted()
      .forEach(eachOperation -> {
        final var operation = model.expectShape(
          eachOperation,
          OperationShape.class
        );
        final var input = model.expectShape(operation.getInputShape());
        if (!alreadyVisited.contains(input.toShapeId())) {
          alreadyVisited.add(input.toShapeId());
          if (
            !input.hasTrait(UnitTypeTrait.class) &&
            input
              .toShapeId()
              .getNamespace()
              .equals(serviceShape.toShapeId().getNamespace())
          ) {
            final var inputToDafnyMethodName =
              SmithyNameResolver.getToDafnyMethodName(serviceShape, input, "");
            final var inputSymbol = symbolProvider.toSymbol(input);
            final String outputType;
            if (input.hasTrait(PositionalTrait.class)) {
              // Output type in To Dafny should be unwrapped
              Shape inputForPositional = model.expectShape(
                input
                  .getAllMembers()
                  .values()
                  .stream()
                  .findFirst()
                  .get()
                  .getTarget()
              );
              Symbol symbolForPositional = symbolProvider.toSymbol(
                inputForPositional
              );
              outputType =
                DafnyNameResolver.getDafnyType(
                  inputForPositional,
                  symbolForPositional
                );
            } else {
              outputType = DafnyNameResolver.getDafnyType(input, inputSymbol);
            }
            writerDelegator.useFileWriter(
              "%s/%s".formatted(
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  TO_DAFNY
                ),
              SmithyNameResolver.shapeNamespace(serviceShape),
              writer -> {
                writer.addImportFromModule(
                  SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                    input.toShapeId().getNamespace()
                  ),
                  SmithyNameResolver.smithyTypesNamespace(input, model)
                );
                writer.write(
                  """
                  func $L(nativeInput $L)($L) {
                      ${C|}
                  }""",
                  inputToDafnyMethodName,
                  SmithyNameResolver.getSmithyType(input, inputSymbol, model),
                  outputType,
                  writer.consumer(w ->
                    generateRequestSerializer(
                      context,
                      operation,
                      context.writerDelegator()
                    )
                  )
                );
              }
            );
          }
        }

        final var output = model.expectShape(operation.getOutputShape());
        if (!alreadyVisited.contains(output.toShapeId())) {
          alreadyVisited.add(output.toShapeId());
          if (
            !output.hasTrait(UnitTypeTrait.class) &&
            output
              .toShapeId()
              .getNamespace()
              .equals(serviceShape.toShapeId().getNamespace())
          ) {
            final var outputToDafnyMethodName =
              SmithyNameResolver.getToDafnyMethodName(serviceShape, output, "");
            final var outputSymbol = symbolProvider.toSymbol(output);
            writerDelegator.useFileWriter(
              "%s/%s".formatted(
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  TO_DAFNY
                ),
              SmithyNameResolver.shapeNamespace(serviceShape),
              writer -> {
                if (output.hasTrait(PositionalTrait.class)) {
                  output.accept(
                    new SmithyToDafnyShapeVisitor(
                      context,
                      "nativeOutput",
                      writer,
                      false,
                      false,
                      false
                    )
                  );
                } else {
                  writer.addImportFromModule(
                    SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                      output.toShapeId().getNamespace()
                    ),
                    SmithyNameResolver.smithyTypesNamespace(output, model)
                  );
                  writer.write(
                    """
                    func $L(nativeOutput $L)($L) {
                        ${C|}
                    }""",
                    outputToDafnyMethodName,
                    SmithyNameResolver.getSmithyType(
                      output,
                      outputSymbol,
                      model
                    ),
                    DafnyNameResolver.getDafnyType(output, outputSymbol),
                    writer.consumer(w ->
                      generateResponseSerializer(
                        context,
                        operation,
                        context.writerDelegator()
                      )
                    )
                  );
                }
              }
            );
          }
        }
      });

    final var refResources = context
      .model()
      .getShapesWithTrait(ReferenceTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    for (final var refResource : refResources) {
      final var resource = refResource
        .expectTrait(ReferenceTrait.class)
        .getReferentId();
      alreadyVisited.add(refResource.toShapeId());
      if (!refResource.expectTrait(ReferenceTrait.class).isService()) {
        final var resourceShape = model.expectShape(
          resource,
          ResourceShape.class
        );
        resourceShape
          .getOperations()
          .stream()
          .sorted()
          .forEach(eachOperation -> {
            final var operation = model.expectShape(
              eachOperation,
              OperationShape.class
            );
            final var input = model.expectShape(operation.getInputShape());
            if (!alreadyVisited.contains(input.toShapeId())) {
              alreadyVisited.add(input.toShapeId());
              if (
                !input.hasTrait(UnitTypeTrait.class) &&
                input
                  .toShapeId()
                  .getNamespace()
                  .equals(serviceShape.toShapeId().getNamespace())
              ) {
                final var inputToDafnyMethodName =
                  SmithyNameResolver.getToDafnyMethodName(
                    serviceShape,
                    input,
                    ""
                  );
                final var inputSymbol = symbolProvider.toSymbol(input);
                final String outputType;
                if (input.hasTrait(PositionalTrait.class)) {
                  // Output type in To Dafny should be unwrapped
                  Shape inputForPositional = model.expectShape(
                    input
                      .getAllMembers()
                      .values()
                      .stream()
                      .findFirst()
                      .get()
                      .getTarget()
                  );
                  Symbol symbolForPositional = symbolProvider.toSymbol(
                    inputForPositional
                  );
                  outputType =
                    DafnyNameResolver.getDafnyType(
                      inputForPositional,
                      symbolForPositional
                    );
                } else {
                  outputType =
                    DafnyNameResolver.getDafnyType(input, inputSymbol);
                }
                writerDelegator.useFileWriter(
                  "%s/%s".formatted(
                      SmithyNameResolver.shapeNamespace(serviceShape),
                      TO_DAFNY
                    ),
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  writer -> {
                    writer.addImportFromModule(
                      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                        input.toShapeId().getNamespace()
                      ),
                      SmithyNameResolver.smithyTypesNamespace(input, model)
                    );
                    writer.write(
                      """
                      func $L(nativeInput $L)($L) {
                          ${C|}
                      }""",
                      inputToDafnyMethodName,
                      SmithyNameResolver.getSmithyType(
                        input,
                        inputSymbol,
                        model
                      ),
                      outputType,
                      writer.consumer(w ->
                        generateRequestSerializer(
                          context,
                          operation,
                          context.writerDelegator()
                        )
                      )
                    );
                  }
                );
              }
            }

            final var output = model.expectShape(operation.getOutputShape());
            if (!alreadyVisited.contains(output.toShapeId())) {
              alreadyVisited.add(output.toShapeId());
              if (
                !output.hasTrait(UnitTypeTrait.class) &&
                output
                  .toShapeId()
                  .getNamespace()
                  .equals(serviceShape.toShapeId().getNamespace())
              ) {
                final var outputToDafnyMethodName =
                  SmithyNameResolver.getToDafnyMethodName(
                    serviceShape,
                    output,
                    ""
                  );
                final var outputSymbol = symbolProvider.toSymbol(output);
                writerDelegator.useFileWriter(
                  "%s/%s".formatted(
                      SmithyNameResolver.shapeNamespace(serviceShape),
                      TO_DAFNY
                    ),
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  writer -> {
                    if (output.hasTrait(PositionalTrait.class)) {
                      output.accept(
                        new SmithyToDafnyShapeVisitor(
                          context,
                          "nativeOutput",
                          writer,
                          false,
                          false,
                          false
                        )
                      );
                    } else {
                      writer.addImportFromModule(
                        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                          output.toShapeId().getNamespace()
                        ),
                        SmithyNameResolver.smithyTypesNamespace(output, model)
                      );
                      writer.write(
                        """
                        func $L(nativeOutput $L)($L) {
                            ${C|}
                        }""",
                        outputToDafnyMethodName,
                        SmithyNameResolver.getSmithyType(
                          output,
                          outputSymbol,
                          model
                        ),
                        DafnyNameResolver.getDafnyType(output, outputSymbol),
                        writer.consumer(w ->
                          generateResponseSerializer(
                            context,
                            operation,
                            context.writerDelegator()
                          )
                        )
                      );
                    }
                  }
                );
              }
            }
          });
        if (
          !alreadyVisited.contains(resourceShape.toShapeId()) &&
          resourceShape
            .toShapeId()
            .getNamespace()
            .equals(serviceShape.toShapeId().getNamespace())
        ) {
          alreadyVisited.add(resourceShape.toShapeId());
          writerDelegator.useFileWriter(
            "%s/%s".formatted(
                SmithyNameResolver.shapeNamespace(serviceShape),
                TO_DAFNY
              ),
            SmithyNameResolver.shapeNamespace(serviceShape),
            writer -> {
              var goBody =
                """
                return nativeResource.(*%s).Impl
                """.formatted(resourceShape.getId().getName());
              if (resourceShape.hasTrait(ExtendableTrait.class)) {
                goBody =
                  """
                                                     val, ok := nativeResource.(*%s)
                  if ok {
                  	return val.Impl
                  }
                  return %s{&%sNativeWrapper{Impl: nativeResource}}.Impl
                                                     """.formatted(
                      resourceShape.getId().getName(),
                      resourceShape.getId().getName(),
                      resourceShape.getId().getName()
                    );
              }
              writer.write(
                """
                func $L_ToDafny(nativeResource $L.I$L) $L.I$L {
                    $L
                }
                """,
                resourceShape.getId().getName(),
                SmithyNameResolver.smithyTypesNamespace(resourceShape, model),
                resourceShape.getId().getName(),
                DafnyNameResolver.dafnyTypesNamespace(resourceShape),
                resourceShape.getId().getName(),
                goBody
              );
            }
          );
        }
      }
    }
    generateErrorSerializer(context, alreadyVisited);
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      generateConfigSerializer(context, alreadyVisited);
    }
    final var orphanShapes =
      ModelUtils.getTopologicallyOrderedOrphanedShapesForService(
        serviceShape,
        model
      );
    // Loop through each Shape in orphanShapes
    for (Shape shape : orphanShapes) {
      generateOrphanShapeSerializer(
        context,
        shape,
        alreadyVisited,
        serviceShape
      );
    }
    generateSerializerFunctions(context, alreadyVisited);
  }

  public void generateOrphanShapeSerializer(
    final GenerationContext context,
    final Shape shape,
    final Set<ShapeId> alreadyVisited,
    ServiceShape serviceShape
  ) {
    if (
      GoCodegenUtils.shapeShouldHaveConversionFunction(shape) == false ||
      alreadyVisited.contains(shape.toShapeId())
    ) {
      return;
    }
    if (shape.hasTrait(UnitTypeTrait.class)) {
      return;
    }
    final var inputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(
      serviceShape,
      shape,
      ""
    );
    final var writerDelegator = context.writerDelegator();
    String outputType;
    final var curSymbol = context.symbolProvider().toSymbol(shape);
    final String inputType;
    alreadyVisited.add(shape.toShapeId());
    if (shape.hasTrait(ReferenceTrait.class)) {
      final var referenceTrait = shape.expectTrait(ReferenceTrait.class);
      final var resourceOrService = context
        .model()
        .expectShape(referenceTrait.getReferentId());
      if (resourceOrService.isResourceShape()) {
        throw new IllegalStateException(
          "Reference to resource shapes are already handled in generateSerializers function."
        );
      }
      if (resourceOrService.hasTrait(ServiceTrait.class)) {
        outputType =
          DafnyNameResolver.getDafnyInterfaceClient(
            resourceOrService.asServiceShape().get(),
            resourceOrService.getTrait(ServiceTrait.class).get()
          );
        inputType =
          GoCodegenUtils.getType(
            context.symbolProvider().toSymbol(resourceOrService),
            true,
            context.model()
          );
      } else {
        outputType =
          DafnyNameResolver.getDafnyInterfaceClient(resourceOrService);
        inputType =
          SmithyNameResolver
            .shapeNamespace(resourceOrService)
            .concat(".")
            .concat(context.symbolProvider().toSymbol(serviceShape).getName());
      }
    } else {
      inputType = GoCodegenUtils.getType(curSymbol, true, context.model());
      outputType = DafnyNameResolver.getDafnyType(shape, curSymbol);
    }
    writerDelegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(serviceShape),
          TO_DAFNY
        ),
      SmithyNameResolver.shapeNamespace(serviceShape),
      writer -> {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            shape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.smithyTypesNamespace(shape, context.model())
        );
        writer.write(
          """
          func $L(nativeInput $L)($L) {
              ${C|}
          }""",
          inputToDafnyMethodName,
          inputType,
          outputType,
          writer.consumer(w -> {
            final String shapeVisitorOutput = shape.accept(
              new SmithyToDafnyShapeVisitor(
                context,
                "nativeInput",
                writer,
                false,
                false,
                false
              )
            );
            writer.write(
              """
              return $L
              """,
              shapeVisitorOutput
            );
          })
        );
      }
    );
  }

  @Override
  public void generateDeserializers(final GenerationContext context) {
    final Set<ShapeId> alreadyVisited = new HashSet<>();
    final var serviceShape = context.settings().getService(context.model());
    final var delegator = context.writerDelegator();

    serviceShape
      .getOperations()
      .stream()
      .sorted()
      .forEach(eachOperation -> {
        final var operation = context
          .model()
          .expectShape(eachOperation, OperationShape.class);

        final var input = context
          .model()
          .expectShape(operation.getInputShape());
        if (!alreadyVisited.contains(input.toShapeId())) {
          alreadyVisited.add(input.toShapeId());
          if (
            !input.hasTrait(UnitTypeTrait.class) &&
            input
              .toShapeId()
              .getNamespace()
              .equals(serviceShape.toShapeId().getNamespace())
          ) {
            final var inputFromDafnyMethodName =
              SmithyNameResolver.getFromDafnyMethodName(
                serviceShape,
                input,
                ""
              );
            final var inputSymbol = context.symbolProvider().toSymbol(input);
            final String inputType;
            if (input.hasTrait(PositionalTrait.class)) {
              // Input type in To native should be unwrapped
              Shape inputForPositional = context
                .model()
                .expectShape(
                  input
                    .getAllMembers()
                    .values()
                    .stream()
                    .findFirst()
                    .get()
                    .getTarget()
                );
              Symbol symbolForPositional = context
                .symbolProvider()
                .toSymbol(inputForPositional);
              inputType =
                DafnyNameResolver.getDafnyType(
                  inputForPositional,
                  symbolForPositional
                );
            } else {
              inputType = DafnyNameResolver.getDafnyType(input, inputSymbol);
            }
            delegator.useFileWriter(
              "%s/%s".formatted(
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  TO_NATIVE
                ),
              SmithyNameResolver.shapeNamespace(serviceShape),
              writer -> {
                writer.addImportFromModule(
                  SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                    input.toShapeId().getNamespace()
                  ),
                  SmithyNameResolver.smithyTypesNamespace(
                    input,
                    context.model()
                  )
                );

                writer.write(
                  """
                  func $L(dafnyInput $L)($L) {
                      ${C|}
                  }""",
                  inputFromDafnyMethodName,
                  inputType,
                  SmithyNameResolver.getSmithyType(
                    input,
                    inputSymbol,
                    context.model()
                  ),
                  writer.consumer(w ->
                    generateRequestDeserializer(
                      context,
                      operation,
                      context.writerDelegator()
                    )
                  )
                );
              }
            );
          }
        }

        final var output = context
          .model()
          .expectShape(operation.getOutputShape());
        if (!alreadyVisited.contains(output.toShapeId())) {
          alreadyVisited.add(output.toShapeId());
          if (
            !output.hasTrait(UnitTypeTrait.class) &&
            output
              .toShapeId()
              .getNamespace()
              .equals(serviceShape.toShapeId().getNamespace())
          ) {
            final var outputFromDafnyMethodName =
              SmithyNameResolver.getFromDafnyMethodName(
                serviceShape,
                output,
                ""
              );
            final var outputSymbol = context.symbolProvider().toSymbol(output);

            delegator.useFileWriter(
              "%s/%s".formatted(
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  TO_NATIVE
                ),
              SmithyNameResolver.shapeNamespace(serviceShape),
              writer -> {
                if (output.hasTrait(PositionalTrait.class)) {
                  output.accept(
                    new DafnyToSmithyShapeVisitor(
                      context,
                      "dafnyOutput",
                      writer,
                      false
                    )
                  );
                } else {
                  writer.addImportFromModule(
                    SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                      output.toShapeId().getNamespace()
                    ),
                    SmithyNameResolver.smithyTypesNamespace(
                      output,
                      context.model()
                    )
                  );

                  writer.write(
                    """
                    func $L(dafnyOutput $L)($L) {
                        ${C|}
                    }""",
                    outputFromDafnyMethodName,
                    DafnyNameResolver.getDafnyType(output, outputSymbol),
                    SmithyNameResolver.getSmithyType(
                      output,
                      outputSymbol,
                      context.model()
                    ),
                    writer.consumer(w ->
                      generateResponseDeserializer(
                        context,
                        operation,
                        context.writerDelegator()
                      )
                    )
                  );
                }
              }
            );
          }
        }
      });

    final var refResources = context
      .model()
      .getShapesWithTrait(ReferenceTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    for (final var refResource : refResources) {
      final var resource = refResource
        .expectTrait(ReferenceTrait.class)
        .getReferentId();
      alreadyVisited.add(refResource.toShapeId());
      if (!refResource.expectTrait(ReferenceTrait.class).isService()) {
        final var resourceShape = context
          .model()
          .expectShape(resource, ResourceShape.class);
        resourceShape
          .getOperations()
          .stream()
          .sorted()
          .forEach(eachOperation -> {
            final var operation = context
              .model()
              .expectShape(eachOperation, OperationShape.class);
            final var input = context
              .model()
              .expectShape(operation.getInputShape());
            if (!alreadyVisited.contains(input.toShapeId())) {
              alreadyVisited.add(input.toShapeId());
              if (
                !input.hasTrait(UnitTypeTrait.class) &&
                input
                  .toShapeId()
                  .getNamespace()
                  .equals(serviceShape.toShapeId().getNamespace())
              ) {
                final var inputFromDafnyMethodName =
                  SmithyNameResolver.getFromDafnyMethodName(
                    serviceShape,
                    input,
                    ""
                  );
                final var inputSymbol = context
                  .symbolProvider()
                  .toSymbol(input);
                final String inputType;
                if (input.hasTrait(PositionalTrait.class)) {
                  // Input type in To native should be unwrapped
                  Shape inputForPositional = context
                    .model()
                    .expectShape(
                      input
                        .getAllMembers()
                        .values()
                        .stream()
                        .findFirst()
                        .get()
                        .getTarget()
                    );
                  Symbol symbolForPositional = context
                    .symbolProvider()
                    .toSymbol(inputForPositional);
                  inputType =
                    DafnyNameResolver.getDafnyType(
                      inputForPositional,
                      symbolForPositional
                    );
                } else {
                  inputType =
                    DafnyNameResolver.getDafnyType(input, inputSymbol);
                }

                delegator.useFileWriter(
                  "%s/%s".formatted(
                      SmithyNameResolver.shapeNamespace(serviceShape),
                      TO_NATIVE
                    ),
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  writer -> {
                    writer.addImportFromModule(
                      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                        input.toShapeId().getNamespace()
                      ),
                      SmithyNameResolver.smithyTypesNamespace(
                        input,
                        context.model()
                      )
                    );

                    writer.write(
                      """
                      func $L(dafnyInput $L)($L) {
                          ${C|}
                      }""",
                      inputFromDafnyMethodName,
                      inputType,
                      SmithyNameResolver.getSmithyType(
                        input,
                        inputSymbol,
                        context.model()
                      ),
                      writer.consumer(w ->
                        generateRequestDeserializer(
                          context,
                          operation,
                          context.writerDelegator()
                        )
                      )
                    );
                  }
                );
              }
            }

            final var output = context
              .model()
              .expectShape(operation.getOutputShape());
            if (!alreadyVisited.contains(output.toShapeId())) {
              alreadyVisited.add(output.toShapeId());
              if (
                !output.hasTrait(UnitTypeTrait.class) &&
                output
                  .toShapeId()
                  .getNamespace()
                  .equals(serviceShape.toShapeId().getNamespace())
              ) {
                final var outputFromDafnyMethodName =
                  SmithyNameResolver.getFromDafnyMethodName(
                    serviceShape,
                    output,
                    ""
                  );
                final var outputSymbol = context
                  .symbolProvider()
                  .toSymbol(output);

                delegator.useFileWriter(
                  "%s/%s".formatted(
                      SmithyNameResolver.shapeNamespace(serviceShape),
                      TO_NATIVE
                    ),
                  SmithyNameResolver.shapeNamespace(serviceShape),
                  writer -> {
                    if (output.hasTrait(PositionalTrait.class)) {
                      output.accept(
                        new DafnyToSmithyShapeVisitor(
                          context,
                          "dafnyOutput",
                          writer,
                          false
                        )
                      );
                    } else {
                      writer.addImportFromModule(
                        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                          output.toShapeId().getNamespace()
                        ),
                        SmithyNameResolver.smithyTypesNamespace(
                          output,
                          context.model()
                        )
                      );

                      writer.write(
                        """
                        func $L(dafnyOutput $L)($L) {
                            ${C|}
                        }""",
                        outputFromDafnyMethodName,
                        DafnyNameResolver.getDafnyType(output, outputSymbol),
                        SmithyNameResolver.getSmithyType(
                          output,
                          outputSymbol,
                          context.model()
                        ),
                        writer.consumer(w ->
                          generateResponseDeserializer(
                            context,
                            operation,
                            context.writerDelegator()
                          )
                        )
                      );
                    }
                  }
                );
              }
            }
          });
        if (
          !alreadyVisited.contains(resourceShape.toShapeId()) &&
          resourceShape
            .toShapeId()
            .getNamespace()
            .equals(serviceShape.toShapeId().getNamespace())
        ) {
          alreadyVisited.add(resourceShape.toShapeId());
          delegator.useFileWriter(
            "%s/%s".formatted(
                SmithyNameResolver.shapeNamespace(serviceShape),
                TO_NATIVE
              ),
            SmithyNameResolver.shapeNamespace(serviceShape),
            writer -> {
              var extendableResourceWrapperCheck = "";
              if (resourceShape.hasTrait(ExtendableTrait.class)) {
                extendableResourceWrapperCheck =
                  """
                  val, ok := dafnyResource.(*%sNativeWrapper)
                  if ok {
                      return val.Impl
                  }
                  """.formatted(resourceShape.getId().getName());
              }
              writer.write(
                """
                func $L_FromDafny(dafnyResource $L.I$L)($L.I$L) {
                    $L
                    return &$L{dafnyResource}
                }
                """,
                resourceShape.getId().getName(),
                DafnyNameResolver.dafnyTypesNamespace(resourceShape),
                resourceShape.getId().getName(),
                SmithyNameResolver.smithyTypesNamespace(
                  resourceShape,
                  context.model()
                ),
                resourceShape.getId().getName(),
                extendableResourceWrapperCheck,
                resourceShape.getId().getName()
              );
            }
          );
        }
      }
    }
    generateErrorDeserializer(context, alreadyVisited);
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      generateConfigDeserializer(context, alreadyVisited);
    }
    final var orphanShapes =
      ModelUtils.getTopologicallyOrderedOrphanedShapesForService(
        serviceShape,
        context.model()
      );
    // Loop through each Shape in orphanShapes
    for (Shape shape : orphanShapes) {
      generateOrphanShapeDeserializer(
        context,
        shape,
        alreadyVisited,
        serviceShape
      );
    }
    generateDeserializerFunctions(context, alreadyVisited);
  }

  public void generateOrphanShapeDeserializer(
    final GenerationContext context,
    final Shape shape,
    final Set<ShapeId> alreadyVisited,
    ServiceShape serviceShape
  ) {
    if (
      GoCodegenUtils.shapeShouldHaveConversionFunction(shape) == false ||
      alreadyVisited.contains(shape.toShapeId())
    ) {
      return;
    }
    if (shape.hasTrait(UnitTypeTrait.class)) {
      return;
    }
    final var writerDelegator = context.writerDelegator();
    final String outputType;
    final var inputFromDafnyMethodName =
      SmithyNameResolver.getFromDafnyMethodName(serviceShape, shape, "");
    if (shape.hasTrait(ReferenceTrait.class)) {
      final var referenceTrait = shape.expectTrait(ReferenceTrait.class);
      final var resourceOrService = context
        .model()
        .expectShape(referenceTrait.getReferentId());
      if (resourceOrService.isResourceShape()) {
        throw new IllegalStateException(
          "Reference to resource shapes are already handled in generateDeserializers function."
        );
      }
      if (resourceOrService.hasTrait(ServiceTrait.class)) {
        outputType =
          SmithyNameResolver.getAwsServiceClient(
            resourceOrService.expectTrait(ServiceTrait.class)
          );
      } else {
        final var namespace = SmithyNameResolver
          .shapeNamespace(resourceOrService)
          .concat(".");
        outputType =
          "*".concat(
              namespace.concat(
                context.symbolProvider().toSymbol(resourceOrService).getName()
              )
            );
      }
    } else {
      outputType =
        GoCodegenUtils.getType(
          context.symbolProvider().toSymbol(shape),
          true,
          context.model()
        );
    }
    writerDelegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(serviceShape),
          TO_NATIVE
        ),
      SmithyNameResolver.shapeNamespace(serviceShape),
      writer -> {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            shape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.smithyTypesNamespace(shape, context.model())
        );
        writer.write(
          """
          func $L(input interface{})($L) {
              ${C|}
          }""",
          inputFromDafnyMethodName,
          outputType,
          writer.consumer(w -> {
            final var shapeVisitorOutput = shape.accept(
              new DafnyToSmithyShapeVisitor(context, "input", writer, false)
            );
            writer.write(
              """
              $L
              """,
              shapeVisitorOutput
            );
          })
        );
      }
    );
  }

  private void generateRequestSerializer(
    final GenerationContext context,
    final OperationShape operation,
    final GoDelegator delegator
  ) {
    final var targetShape = context
      .model()
      .expectShape(operation.getInputShape());
    delegator.useFileWriter(
      "%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_DAFNY),
      SmithyNameResolver.shapeNamespace(operation),
      writer -> {
        final var input = targetShape.accept(
          new SmithyToDafnyShapeVisitor(
            context,
            "nativeInput",
            writer,
            false,
            false,
            false
          )
        );
        writer.write(
          """
          return $L
          """,
          input
        );
      }
    );
  }

  private void generateResponseSerializer(
    final GenerationContext context,
    final OperationShape operation,
    final GoDelegator delegator
  ) {
    final var targetShape = context
      .model()
      .expectShape(operation.getOutputShape());
    delegator.useFileWriter(
      "%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_DAFNY),
      SmithyNameResolver.shapeNamespace(operation),
      writer -> {
        final var input = targetShape.accept(
          new SmithyToDafnyShapeVisitor(
            context,
            "nativeOutput",
            writer,
            false,
            false,
            false
          )
        );
        writer.write(
          """
          return $L
          """,
          input
        );
      }
    );
  }

  private void generateRequestDeserializer(
    final GenerationContext context,
    final OperationShape operation,
    final GoDelegator delegator
  ) {
    delegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(operation),
          TO_NATIVE
        ),
      SmithyNameResolver.shapeNamespace(operation),
      writer -> {
        final var inputShape = operation.getInputShape();

        final var targetShape = context.model().expectShape(inputShape);
        final var input = targetShape.accept(
          new DafnyToSmithyShapeVisitor(context, "dafnyInput", writer, false)
        );

        writer.write(
          """
          $L
          """,
          input
        );
      }
    );
  }

  private void generateResponseDeserializer(
    final GenerationContext context,
    final OperationShape operation,
    final GoDelegator delegator
  ) {
    delegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(operation),
          TO_NATIVE
        ),
      SmithyNameResolver.shapeNamespace(operation),
      writer -> {
        final var outputShape = operation.getOutputShape();

        final var targetShape = context.model().expectShape(outputShape);
        final var output = targetShape.accept(
          new DafnyToSmithyShapeVisitor(context, "dafnyOutput", writer, false)
        );

        writer.write(
          """
          $L
          """,
          output
        );
      }
    );
  }

  private void generateConfigSerializer(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var service = context.settings().getService(context.model());
    final var localServiceTrait = service.expectTrait(LocalServiceTrait.class);
    final var configShape = context
      .model()
      .expectShape(localServiceTrait.getConfigId(), StructureShape.class);
    final var getInputToDafnyMethodName =
      SmithyNameResolver.getToDafnyMethodName(service, configShape, "");
    if (
      !configShape
        .toShapeId()
        .getNamespace()
        .equals(service.toShapeId().getNamespace())
    ) {
      return;
    }
    alreadyVisited.add(configShape.getId());
    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(SmithyNameResolver.shapeNamespace(service), TO_DAFNY),
        SmithyNameResolver.shapeNamespace(service),
        writer -> {
          writer.write(
            """
            func $L(nativeInput $L)($L) {
                ${C|}
            }""",
            getInputToDafnyMethodName,
            SmithyNameResolver.getSmithyType(
              configShape,
              context.symbolProvider().toSymbol(configShape),
              context.model()
            ),
            DafnyNameResolver.getDafnyType(
              configShape,
              context.symbolProvider().toSymbol(configShape)
            ),
            writer.consumer(w -> {
              final String output = configShape.accept(
                new SmithyToDafnyShapeVisitor(
                  context,
                  "nativeInput",
                  writer,
                  true,
                  false,
                  false
                )
              );
              writer.write(
                """
                return $L
                """,
                output
              );
            })
          );
        }
      );
  }

  private void generateErrorSerializer(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var serviceShape = context.settings().getService(context.model());
    final var errorShapes = context
      .model()
      .getShapesWithTrait(ErrorTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));

    for (final var errorShape : errorShapes) {
      if (
        !errorShape
          .toShapeId()
          .getNamespace()
          .equals(serviceShape.toShapeId().getNamespace())
      ) {
        continue;
      }
      if (!alreadyVisited.contains(errorShape.toShapeId())) {
        alreadyVisited.add(errorShape.toShapeId());
        final var getInputToDafnyMethodName =
          SmithyNameResolver.getToDafnyMethodName(serviceShape, errorShape, "");

        context
          .writerDelegator()
          .useFileWriter(
            "%s/%s".formatted(
                SmithyNameResolver.shapeNamespace(errorShape),
                TO_DAFNY
              ),
            SmithyNameResolver.shapeNamespace(errorShape),
            writer -> {
              writer.write(
                """
                func $L(nativeInput $L)($L) {
                    ${C|}
                }""",
                getInputToDafnyMethodName,
                SmithyNameResolver.getSmithyType(
                  errorShape,
                  context.symbolProvider().toSymbol(errorShape),
                  context.model()
                ),
                DafnyNameResolver.getDafnyBaseErrorType(errorShape),
                writer.consumer(w -> {
                  final String output = errorShape.accept(
                    new SmithyToDafnyShapeVisitor(
                      context,
                      "nativeInput",
                      writer,
                      false,
                      false,
                      false
                    )
                  );
                  writer.write(
                    """
                    return $L
                    """,
                    output
                  );
                })
              );
            }
          );
      }
    }

    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(
            SmithyNameResolver.shapeNamespace(serviceShape),
            TO_DAFNY
          ),
        SmithyNameResolver.shapeNamespace(serviceShape),
        writer -> {
          writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");
          writer.write(
            """
            func CollectionOfErrors_Input_ToDafny(nativeInput $L.CollectionOfErrors)($L.Error) {
            	var e []interface{}
            	for _, i2 := range nativeInput.ListOfErrors {
                   e = append(e, Error_ToDafny(i2))
            	}
            	return $L.Companion_Error_.Create_CollectionOfErrors_(dafny.SeqOf(e...), dafny.SeqOfChars([]dafny.Char(nativeInput.Message)...))
            }
            func OpaqueError_Input_ToDafny(nativeInput $L.OpaqueError)($L.Error) {
            	return $L.Companion_Error_.Create_Opaque_(nativeInput.ErrObject)
            }""",
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape)
          );
        }
      );

    final Set<StructureShape> errorShapesForNamespace = context
      .model()
      .getStructureShapes()
      .stream()
      .filter(shape -> shape.hasTrait(ErrorTrait.class))
      .filter(shape ->
        ModelUtils.isInServiceNamespace(shape.getId(), serviceShape)
      )
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));

    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(
            SmithyNameResolver.shapeNamespace(
              context.settings().getService(context.model())
            ),
            TO_DAFNY
          ),
        SmithyNameResolver.shapeNamespace(
          context.settings().getService(context.model())
        ),
        writer -> {
          writer.write(
            """
            func Error_ToDafny(err error)($L.Error) {
                switch err.(type) {
                // Service Errors
                ${C|}
                //DependentErrors
                ${C|}

                //Unmodelled Errors
                case $L.CollectionOfErrors:
                    return CollectionOfErrors_Input_ToDafny(err.($L.CollectionOfErrors))

                default:
                    error, ok := err.($L.OpaqueError)
                    if !ok {
                        panic("Error is not an OpaqueError")
                    }
                    return OpaqueError_Input_ToDafny(error)
                }
            }
            """,
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            writer.consumer(w -> {
              for (var errorShape : errorShapesForNamespace) {
                final var error = errorShape.getId();
                w.write(
                  """
                    case $L:
                        return $L(err.($L))
                  """,
                  SmithyNameResolver.getSmithyType(
                    context.model().expectShape(error),
                    context
                      .symbolProvider()
                      .toSymbol(context.model().expectShape(error)),
                    context.model()
                  ),
                  SmithyNameResolver.getToDafnyMethodName(
                    serviceShape,
                    context.model().expectShape(error),
                    ""
                  ),
                  SmithyNameResolver.getSmithyType(
                    context.model().expectShape(error),
                    context
                      .symbolProvider()
                      .toSymbol(context.model().expectShape(error)),
                    context.model()
                  )
                );
              }
            }),
            writer.consumer(w -> {
              final var dependencies = serviceShape.hasTrait(
                  LocalServiceTrait.class
                )
                ? serviceShape
                  .expectTrait(LocalServiceTrait.class)
                  .getDependencies()
                : new LinkedList<ShapeId>();
              if (dependencies != null) {
                handleDepErrorSerializer(context, w, dependencies);
              }
            }),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            )
          );
        }
      );
  }

  private void handleDepErrorSerializer(
    final GenerationContext context,
    final GoWriter w,
    final Collection<ShapeId> dependencies
  ) {
    final var sdkErrHandler = new StringBuilder();
    final var sdkOpaqueErrHandler = new StringBuilder();
    final var serviceShape = context.settings().getService(context.model());
    Boolean sdkDepFound = false;
    for (final var dep : dependencies) {
      final var depShape = context.model().expectShape(dep);
      if (depShape.hasTrait(ServiceTrait.class)) {
        if (sdkDepFound == false) {
          w.addImport(SmithyGoDependency.SMITHY_SOURCE_PATH);
          sdkErrHandler.append(
            """
            case smithy.APIError:
            """
          );
          sdkOpaqueErrHandler.append(
            """
            case *smithy.OperationError:
            """
          );
        }
        w.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            depShape.getId().getNamespace()
          ),
          SmithyNameResolver.shapeNamespace(depShape)
        );
        sdkDepFound = true;
        final var sdkDepErrorVar = depShape
          .expectTrait(ServiceTrait.class)
          .getSdkId()
          .concat("Error");
        sdkOpaqueErrHandler.append(
          """
            if (err.(*smithy.OperationError).Service() == "%s") {
              %s := %s.Error_ToDafny(err)
              return %s.Create_%s_(%s)
            }
          """.formatted(
              depShape.expectTrait(ServiceTrait.class).getSdkId(),
              sdkDepErrorVar,
              SmithyNameResolver.shapeNamespace(depShape),
              DafnyNameResolver.getDafnyErrorCompanion(serviceShape),
              DafnyNameResolver.dafnyNamespace(depShape),
              sdkDepErrorVar
            )
        );
        sdkErrHandler.append(
          """
          %s := %s.Error_ToDafny(err)
          if(!%s.Is_OpaqueWithText()) {
            return %s.Create_%s_(%s)
          }
          """.formatted(
              sdkDepErrorVar,
              SmithyNameResolver.shapeNamespace(depShape),
              sdkDepErrorVar,
              DafnyNameResolver.getDafnyErrorCompanion(serviceShape),
              DafnyNameResolver.dafnyNamespace(depShape),
              sdkDepErrorVar
            )
        );
      } else {
        w.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            depShape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.smithyTypesNamespace(depShape, context.model())
        );
        w.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            depShape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.shapeNamespace(depShape)
        );
        w.write(
          """
          case $L.$LBaseException:
              return $L.Create_$L_($L.Error_ToDafny(err))
          """,
          SmithyNameResolver.smithyTypesNamespace(depShape, context.model()),
          dep.getName(),
          DafnyNameResolver.getDafnyErrorCompanion(serviceShape),
          DafnyNameResolver.dafnyDependentErrorName(depShape),
          SmithyNameResolver.shapeNamespace(depShape)
        );
      }
    }
    if (sdkDepFound) {
      final var createOpaqueError =
        """
        return %s.Companion_Error_.Create_Opaque_(err)
        """.formatted(DafnyNameResolver.dafnyTypesNamespace(serviceShape));
      sdkErrHandler.append(createOpaqueError);
      sdkOpaqueErrHandler.append(createOpaqueError);
      w.write(sdkOpaqueErrHandler.toString());
      w.write(sdkErrHandler.toString());
    }
  }

  private void generateConfigDeserializer(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var serviceShape = context.settings().getService(context.model());
    final var localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );
    final var configShape = context
      .model()
      .expectShape(localServiceTrait.getConfigId(), StructureShape.class);
    if (
      !configShape
        .toShapeId()
        .getNamespace()
        .equals(serviceShape.toShapeId().getNamespace())
    ) {
      return;
    }
    final var getOutputFromDafnyMethodName =
      SmithyNameResolver.getFromDafnyMethodName(serviceShape, configShape, "");
    alreadyVisited.add(configShape.getId());
    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(
            SmithyNameResolver.shapeNamespace(serviceShape),
            TO_NATIVE
          ),
        SmithyNameResolver.shapeNamespace(configShape),
        writer -> {
          writer.addImportFromModule(
            SmithyNameResolver.getGoModuleNameForSmithyNamespace(
              configShape.toShapeId().getNamespace()
            ),
            SmithyNameResolver.smithyTypesNamespace(
              configShape,
              context.model()
            )
          );
          writer.write(
            """
            func $L(dafnyOutput $L)($L) {
                ${C|}
            }""",
            getOutputFromDafnyMethodName,
            DafnyNameResolver.getDafnyType(
              configShape,
              context.symbolProvider().toSymbol(configShape)
            ),
            SmithyNameResolver.getSmithyType(
              configShape,
              context.symbolProvider().toSymbol(configShape),
              context.model()
            ),
            writer.consumer(w -> {
              final String output = configShape.accept(
                new DafnyToSmithyShapeVisitor(
                  context,
                  "dafnyOutput",
                  writer,
                  true
                )
              );
              writer.write(
                """
                $L
                """,
                output
              );
            })
          );
        }
      );
  }

  private void generateErrorDeserializer(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var serviceShape = context.settings().getService(context.model());
    final var errorShapes = context
      .model()
      .getShapesWithTrait(ErrorTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    for (final var errorShape : errorShapes) {
      if (
        !errorShape
          .toShapeId()
          .getNamespace()
          .equals(serviceShape.toShapeId().getNamespace())
      ) {
        continue;
      }
      if (!alreadyVisited.contains(errorShape.toShapeId())) {
        alreadyVisited.add(errorShape.toShapeId());
        final var getOutputFromDafnyMethodName =
          SmithyNameResolver.getFromDafnyMethodName(
            serviceShape,
            errorShape,
            ""
          );
        context
          .writerDelegator()
          .useFileWriter(
            "%s/%s".formatted(
                SmithyNameResolver.shapeNamespace(errorShape),
                TO_NATIVE
              ),
            SmithyNameResolver.shapeNamespace(errorShape),
            writer -> {
              writer.write(
                """
                func $L(dafnyOutput $L)($L) {
                    ${C|}
                }""",
                getOutputFromDafnyMethodName,
                DafnyNameResolver.getDafnyBaseErrorType(errorShape),
                SmithyNameResolver.getSmithyType(
                  errorShape,
                  context.symbolProvider().toSymbol(errorShape),
                  context.model()
                ),
                writer.consumer(w -> {
                  final String output = errorShape.accept(
                    new DafnyToSmithyShapeVisitor(
                      context,
                      "dafnyOutput",
                      writer,
                      false
                    )
                  );
                  writer.write(
                    """
                    $L
                    """,
                    output
                  );
                })
              );
            }
          );
      }
    }

    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(
            SmithyNameResolver.shapeNamespace(
              context.settings().getService(context.model())
            ),
            TO_NATIVE
          ),
        SmithyNameResolver.shapeNamespace(
          context.settings().getService(context.model())
        ),
        writer -> {
          writer.write(
            """
            func CollectionOfErrors_Output_FromDafny(dafnyOutput $L.Error)($L.CollectionOfErrors) {
                listOfErrors := dafnyOutput.Dtor_list()
                message := dafnyOutput.Dtor_message()
                t := $L.CollectionOfErrors {}
                for i := dafny.Iterate(listOfErrors) ; ; {
                    val, ok := i()
                    if !ok {
                        break;
                    }
                    err := val.($L.Error)
                    t.ListOfErrors = append(t.ListOfErrors, Error_FromDafny(err))

                }
                t.Message = func() (string) {
                    var s string
                    for i := dafny.Iterate(message) ; ; {
                        val, ok := i()
                        if !ok {
                            return s
                        } else {
                            s = s + string(val.(dafny.Char))
                        }
                    }
                }()
                return t
            }
            func OpaqueError_Output_FromDafny(dafnyOutput $L.Error)($L.OpaqueError) {
                return $L.OpaqueError {
                    ErrObject: dafnyOutput.Dtor_obj(),
                }
            }""",
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            ),
            SmithyNameResolver.smithyTypesNamespace(
              serviceShape,
              context.model()
            )
          );
        }
      );

    final Set<StructureShape> errorShapesForNamespace = context
      .model()
      .getStructureShapes()
      .stream()
      .filter(shape -> shape.hasTrait(ErrorTrait.class))
      .filter(shape ->
        ModelUtils.isInServiceNamespace(shape.getId(), serviceShape)
      )
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));

    context
      .writerDelegator()
      .useFileWriter(
        "%s/%s".formatted(
            SmithyNameResolver.shapeNamespace(
              context.settings().getService(context.model())
            ),
            TO_NATIVE
          ),
        SmithyNameResolver.shapeNamespace(
          context.settings().getService(context.model())
        ),
        writer -> {
          writer.write(
            """
            func Error_FromDafny(err $L.Error)(error) {
                // Service Errors
                ${C|}

                //DependentErrors
                ${C|}

                //Unmodelled Errors
                if err.Is_CollectionOfErrors() {
                    return CollectionOfErrors_Output_FromDafny(err)
                }

                return OpaqueError_Output_FromDafny(err)
            }
            """,
            DafnyNameResolver.dafnyTypesNamespace(serviceShape),
            writer.consumer(w -> {
              for (final var errorShape : errorShapesForNamespace) {
                final var error = errorShape.getId();
                w.write(
                  """
                  if err.Is_$L() {
                      return $L(err)
                  }
                  """,
                  error.getName(),
                  SmithyNameResolver.getFromDafnyMethodName(
                    serviceShape,
                    context.model().expectShape(error),
                    ""
                  )
                );
              }
            }),
            writer.consumer(w -> {
              final var dependencies = serviceShape.hasTrait(
                  LocalServiceTrait.class
                )
                ? serviceShape
                  .expectTrait(LocalServiceTrait.class)
                  .getDependencies()
                : null;
              if (dependencies == null) {
                return;
              }
              for (var dep : dependencies) {
                final var depService = context
                  .model()
                  .expectShape(dep, ServiceShape.class);
                writer.addImportFromModule(
                  SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                    depService.toShapeId().getNamespace()
                  ),
                  SmithyNameResolver.shapeNamespace(depService)
                );
                w.write(
                  """
                  if err.Is_$L() {
                      return $L.Error_FromDafny(err.Dtor_$L())
                  }
                  """,
                  DafnyNameResolver.dafnyDependentErrorName(depService),
                  SmithyNameResolver.shapeNamespace(depService),
                  DafnyNameResolver.dafnyDependentErrorName(depService)
                );
              }
            })
          );
        }
      );
  }

  // Generates rest of the not visited shapes into a function
  // TODO: We should be able to optimize it to run along with the ShapeVisitors.
  // But since this runs outside of any production code - we are okay with this for now
  private void generateSerializerFunctions(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var writerDelegator = context.writerDelegator();
    final var model = context.model();
    final var serviceShape = model.expectShape(
      context.settings().getService(),
      ServiceShape.class
    );
    writerDelegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(serviceShape),
          TO_DAFNY
        ),
      SmithyNameResolver.shapeNamespace(serviceShape),
      writer -> {
        for (final var visitingMemberShape : SmithyToDafnyShapeVisitor.getAllShapesRequiringConversionFunc()) {
          final var visitingShape = context
            .model()
            .expectShape(visitingMemberShape.getTarget());
          if (alreadyVisited.contains(visitingMemberShape.getId())) {
            continue;
          }
          alreadyVisited.add(visitingMemberShape.toShapeId());
          String inputType;
          final Boolean isOptional = ShapeVisitorHelper.isToDafnyShapeOptional(
            visitingMemberShape
          );
          var outputType = isOptional
            ? "Wrappers.Option"
            : DafnyNameResolver.getDafnyType(
              visitingShape,
              context.symbolProvider().toSymbol(visitingShape)
            );
          inputType =
            GoCodegenUtils.getType(
              context.symbolProvider().toSymbol(visitingShape),
              true,
              context.model()
            );
          Boolean isPointable = context
            .symbolProvider()
            .toSymbol(visitingMemberShape)
            .getProperty(POINTABLE, Boolean.class)
            .orElse(false);
          if (visitingShape.hasTrait(ReferenceTrait.class)) {
            final var referenceTrait = visitingShape.expectTrait(
              ReferenceTrait.class
            );
            final var resourceOrService = context
              .model()
              .expectShape(referenceTrait.getReferentId());
            isPointable =
              context
                .symbolProvider()
                .toSymbol(resourceOrService)
                .getProperty(POINTABLE, Boolean.class)
                .orElse(false);
            if (resourceOrService.isServiceShape()) {
              if (resourceOrService.hasTrait(ServiceTrait.class)) {
                outputType =
                  isOptional
                    ? "Wrappers.Option"
                    : DafnyNameResolver.getDafnyInterfaceClient(
                      resourceOrService.asServiceShape().get(),
                      resourceOrService.getTrait(ServiceTrait.class).get()
                    );
                inputType =
                  GoCodegenUtils.getType(
                    context.symbolProvider().toSymbol(resourceOrService),
                    true,
                    context.model()
                  );
              } else {
                outputType =
                  isOptional
                    ? "Wrappers.Option"
                    : DafnyNameResolver.getDafnyInterfaceClient(
                      resourceOrService
                    );
                inputType =
                  SmithyNameResolver
                    .shapeNamespace(resourceOrService)
                    .concat(".")
                    .concat(
                      context.symbolProvider().toSymbol(serviceShape).getName()
                    );
              }
            }
          }
          inputType = isPointable ? "*".concat(inputType) : inputType;
          writer.write(
            """
            func $L(input $L)($L) {
                return $L
            }
            """,
            Constants.funcNameGenerator(visitingMemberShape, "ToDafny"),
            inputType,
            outputType,
            SmithyToDafnyShapeVisitor.getConversionFunc(visitingMemberShape)
          );
        }
      }
    );
  }

  // Generates rest of the not visited shapes into a function
  // TODO: We should be able to optimize it to run along with the ShapeVisitors.
  // But since this runs outside of any production code - we are okay with this for now
  private void generateDeserializerFunctions(
    final GenerationContext context,
    final Set<ShapeId> alreadyVisited
  ) {
    final var delegator = context.writerDelegator();
    final var model = context.model();
    final var serviceShape = model.expectShape(
      context.settings().getService(),
      ServiceShape.class
    );
    delegator.useFileWriter(
      "%s/%s".formatted(
          SmithyNameResolver.shapeNamespace(serviceShape),
          TO_NATIVE
        ),
      SmithyNameResolver.shapeNamespace(serviceShape),
      writer -> {
        for (final var visitingMemberShape : DafnyToSmithyShapeVisitor.getAllShapesRequiringConversionFunc()) {
          final var visitingShape = context
            .model()
            .expectShape(visitingMemberShape.getTarget());
          if (alreadyVisited.contains(visitingMemberShape.getId())) {
            continue;
          }
          alreadyVisited.add(visitingMemberShape.toShapeId());
          var outputType = GoCodegenUtils.getType(
            context.symbolProvider().toSymbol(visitingShape),
            true,
            context.model()
          );
          Boolean isPointable = context
            .symbolProvider()
            .toSymbol(visitingMemberShape)
            .getProperty(POINTABLE, Boolean.class)
            .orElse(false);
          if (visitingShape.hasTrait(ReferenceTrait.class)) {
            final var referenceTrait = visitingShape.expectTrait(
              ReferenceTrait.class
            );
            final var resourceOrService = context
              .model()
              .expectShape(referenceTrait.getReferentId());
            if (resourceOrService.isServiceShape()) {
              isPointable =
                context
                  .symbolProvider()
                  .toSymbol(resourceOrService)
                  .getProperty(POINTABLE, Boolean.class)
                  .orElse(false);
              if (resourceOrService.hasTrait(ServiceTrait.class)) {
                outputType =
                  SmithyNameResolver.getAwsServiceClient(
                    resourceOrService.expectTrait(ServiceTrait.class)
                  );
              } else {
                final var namespace = SmithyNameResolver
                  .shapeNamespace(resourceOrService)
                  .concat(".");
                outputType =
                  namespace.concat(
                    context
                      .symbolProvider()
                      .toSymbol(resourceOrService)
                      .getName()
                  );
              }
            }
          }
          if (isPointable) {
            outputType = "*".concat(outputType);
          }
          // TODO: we should be able to change input type to specific shape from interface {}
          writer.write(
            """
            func $L(input interface{})($L) {
                $L
            }""",
            Constants.funcNameGenerator(visitingMemberShape, "FromDafny"),
            outputType,
            DafnyToSmithyShapeVisitor.getConversionFunc(visitingMemberShape)
          );
        }
      }
    );
  }
}
