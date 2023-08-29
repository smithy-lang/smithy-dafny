package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.codegen.ApplicationProtocol;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getInputFromDafnyMethodName;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getInputToDafnyMethodName;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getOutputFromDafnyMethodName;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getOutputToDafnyMethodName;

public class DafnyTypeConversionProtocol implements ProtocolGenerator {
    public static String TO_DAFNY = "to_dafny.go";
    public static String FROM_DAFNY = "from_dafny.go";

    @Override
    public ShapeId getProtocol() {
        return ShapeId.from("aws.polymorph#localService");
    }

    @Override
    public ApplicationProtocol getApplicationProtocol() {
        return null;
    }

    @Override
    public void generateSerializers(GenerationContext context) {
        final var model = context.model();
        final var serviceShape = model.expectShape(context.settings().getService(), ServiceShape.class);
        final var symbolProvider = context.symbolProvider();
        final var writerDelegator = context.writerDelegator();
        final var topDownIndex = TopDownIndex.of(model);
        for (final var operation : topDownIndex.getContainedOperations(serviceShape)) {
            final var inputToDafnyMethodName = getInputToDafnyMethodName(context, operation);
            final var input = model.expectShape(operation.getInputShape());
            final var inputSymbol = symbolProvider.toSymbol(input);
            writerDelegator.useFileWriter(TO_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");
                writer.write("""
                  func $L(nativeInput $T)($L) {
                      ${C|}
                  }""", inputToDafnyMethodName, inputSymbol,
                             DafnyNameResolver.getDafnyType(context.settings(), inputSymbol),
                             writer.consumer(w -> generateRequestSerializer(context, operation, context.writerDelegator())));
            });

            final var outputToDafnyMethodName = getOutputToDafnyMethodName(context, operation);
            final var output = model.expectShape(operation.getOutputShape());
            final var outputSymbol = symbolProvider.toSymbol(output);
            writerDelegator.useFileWriter(TO_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");
                writer.write("""
                  func $L(nativeOutput $T)($L) {
                      ${C|}
                  }""", outputToDafnyMethodName, outputSymbol,
                             DafnyNameResolver.getDafnyType(context.settings(), outputSymbol),
                             writer.consumer(w -> generateResponseSerializer(context, operation, context.writerDelegator())));
            });
        }
        generateErrorSerializer(context);
        generateConfigSerializer(context);
    }

    @Override
    public void generateDeserializers(GenerationContext context) {
        final var topDownIndex = TopDownIndex.of(context.model());
        final var service = context.settings().getService(context.model());
        final var delegator = context.writerDelegator();

        for (final var operation : topDownIndex.getContainedOperations(service)) {

            final var inputFromDafnyMethodName = getInputFromDafnyMethodName(context, operation);
            final var input = context.model().expectShape(operation.getInputShape());
            final var inputSymbol = context.symbolProvider().toSymbol(input);

            delegator.useFileWriter(FROM_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");

                writer.write("""
                  func $L(dafnyInput $L)($T) {
                      ${C|}
                  }""", inputFromDafnyMethodName, DafnyNameResolver.getDafnyType(context.settings(), inputSymbol),
                             inputSymbol,
                             writer.consumer(w -> generateRequestDeserializer(context, operation, context.writerDelegator())));
            });

            final var outputFromDafnyMethodName = getOutputFromDafnyMethodName(context, operation);
            final var output = context.model().expectShape(operation.getOutputShape());
            final var outputSymbol = context.symbolProvider().toSymbol(output);

            delegator.useFileWriter(FROM_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");

                writer.write("""
                  func $L(dafnyOutput $L)($T) {
                      ${C|}
                  }""", outputFromDafnyMethodName, DafnyNameResolver.getDafnyType(context.settings(), outputSymbol),
                             outputSymbol,
                             writer.consumer(w -> generateResponseDeserializer(context, operation, context.writerDelegator())));
            });
        }
        generateErrorDeserializer(context);
        generateConfigDeserializer(context);

    }

    private void generateRequestSerializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        final var targetShape = context.model().expectShape(operation.getInputShape());
        delegator.useFileWriter(TO_DAFNY, writer -> {
                                                    final var input = targetShape.accept(new SmithyToDafnyShapeVisitor(
                                                            context,
                                                            "nativeInput",
                                                            writer,
                                                            false
                                                    ));
                                                    writer.write("""
                                                                         return $L
                                                                         """,
                                                                 input);
                                                }
        );
    }

    private void generateResponseSerializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        final var targetShape = context.model().expectShape(operation.getOutputShape());
        delegator.useFileWriter(TO_DAFNY, writer -> {
                                    final var input = targetShape.accept(new SmithyToDafnyShapeVisitor(
                                            context,
                                            "nativeOutput",
                                            writer,
                                            false
                                    ));
                                    writer.write("""
                                                                         return $L
                                                                         """,
                                                 input);
                                }
        );
    }

    private void generateRequestDeserializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        delegator.useFileWriter(FROM_DAFNY, writer -> {

            final var inputShape = operation.getInputShape();

            final var targetShape = context.model().expectShape(inputShape);
            final var input = targetShape.accept(new DafnyToSmithyShapeVisitor(
                    context,
                    "dafnyInput",
                    writer,
                    false
            ));

            writer.write("""
                                 return $L
                                 """, input);
        });
    }

    private void generateResponseDeserializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        delegator.useFileWriter(FROM_DAFNY, writer -> {

            final var outputShape = operation.getOutputShape();

            final var targetShape = context.model().expectShape(outputShape);
            final var output = targetShape.accept(new DafnyToSmithyShapeVisitor(
                    context,
                    "dafnyOutput",
                    writer,
                    false
            ));

            writer.write("""
                                 return $L
                                 """, output);
        });
    }

    private void generateConfigSerializer(final GenerationContext context) {
        final var service = context.settings().getService(context.model());
        final LocalServiceTrait localServiceTrait = service.expectTrait(LocalServiceTrait.class);
        final StructureShape configShape = context.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);

        context.writerDelegator().useFileWriter(TO_DAFNY, writer -> {
            writer.write("""
                                 func $L(nativeInput $T)($L) {
                                     ${C|}
                                 }""",
                         getInputToDafnyMethodName(context, configShape), context.symbolProvider().toSymbol(configShape), DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(configShape)),
                         writer.consumer(w -> {
                             String output = configShape.accept(new SmithyToDafnyShapeVisitor(
                                     context,
                                     "nativeInput",
                                     writer,
                                     true
                             ));
                             writer.write("""
                                                  return $L
                                                  """, output);
                         }));
        });
    }

    private void generateErrorSerializer(final GenerationContext context) {

        final var errorShapes = context.model().getShapesWithTrait(ErrorTrait.class);

        for (var errorShape :
                errorShapes) {

            context.writerDelegator().useFileWriter(TO_DAFNY, writer -> {
                writer.write("""
                                     func $L(nativeInput $T)($L) {
                                         ${C|}
                                     }""",
                             getInputToDafnyMethodName(context, errorShape), context.symbolProvider().toSymbol(errorShape), DafnyNameResolver.getDafnyBaseErrorType(context.settings()),
                             writer.consumer(w -> {
                                 String output = errorShape.accept(new SmithyToDafnyShapeVisitor(
                                         context,
                                         "nativeInput",
                                         writer,
                                         false
                                 ));
                                 writer.write("""
                                                      return $L
                                                      """, output);
                             }));
            });
        }
    }

    private void generateConfigDeserializer(final GenerationContext context) {
        final var service = context.settings().getService(context.model());
        final LocalServiceTrait localServiceTrait = service.expectTrait(LocalServiceTrait.class);
        final StructureShape configShape = context.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);

        context.writerDelegator().useFileWriter(FROM_DAFNY, writer -> {
            writer.write("""
                                 func $L(dafnyOutput $L)($T) {
                                     ${C|}
                                 }""",
                         getOutputFromDafnyMethodName(context, configShape), DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(configShape)), context.symbolProvider().toSymbol(configShape),
                         writer.consumer(w -> {
                             String output = configShape.accept(new DafnyToSmithyShapeVisitor(
                                     context,
                                     "dafnyOutput",
                                     writer,
                                     true
                             ));
                             writer.write("""
                                                  return $L
                                                  """, output);
                         }));
        });
    }

    private void generateErrorDeserializer(final GenerationContext context) {

        final var errorShapes = context.model().getShapesWithTrait(ErrorTrait.class);

        for (var errorShape :
                errorShapes) {
            context.writerDelegator().useFileWriter(FROM_DAFNY, writer -> {
                writer.write("""
                                     func $L(dafnyOutput $L)($T) {
                                         ${C|}
                                     }""",
                             getOutputFromDafnyMethodName(context, errorShape), DafnyNameResolver.getDafnyBaseErrorType(context.settings()), context.symbolProvider().toSymbol(errorShape),
                             writer.consumer(w -> {
                                 String output = errorShape.accept(new DafnyToSmithyShapeVisitor(
                                         context,
                                         "dafnyOutput",
                                         writer,
                                         false
                                 ));
                                 writer.write("""
                                                      return $L
                                                      """, output);
                             }));
            });
        }
    }
}
