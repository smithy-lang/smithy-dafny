package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.codegen.ApplicationProtocol;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.INTERNAL_DAFNY;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.INTERNAL_DAFNY_TYPES;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;
import java.util.stream.Collectors;

public class DafnyTypeConversionProtocol implements ProtocolGenerator {
    public static String TO_DAFNY = "to_dafny.go";
    public static String TO_NATIVE = "to_native.go";

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
        final Set<ShapeId> alreadyVisited = new HashSet<>();
        final var model = context.model();
        final var serviceShape = model.expectShape(context.settings().getService(), ServiceShape.class);
        final var symbolProvider = context.symbolProvider();
        final var writerDelegator = context.writerDelegator();
        serviceShape.getOperations().forEach(eachOperation -> {
            final var operation = model.expectShape(eachOperation, OperationShape.class);
            final var input = model.expectShape(operation.getInputShape());
            if (!alreadyVisited.contains(input.toShapeId())) {
                alreadyVisited.add(input.toShapeId());
                if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                    final var inputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, input, "");
                    final var inputSymbol = symbolProvider.toSymbol(input);
                    writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(input.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(input));
                        writer.write("""
                                             func $L(nativeInput $L)($L) {
                                                 ${C|}
                                             }""", inputToDafnyMethodName, SmithyNameResolver.getSmithyType(input, inputSymbol),
                                     DafnyNameResolver.getDafnyType(input, inputSymbol),
                                     writer.consumer(w -> generateRequestSerializer(context, operation, context.writerDelegator())));
                    });
                }
            }

            final var output = model.expectShape(operation.getOutputShape());
            if (!alreadyVisited.contains(output.toShapeId())) {
                alreadyVisited.add(output.toShapeId());
                if (!output.hasTrait(UnitTypeTrait.class) && output.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                    final var outputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, output, "");
                    final var outputSymbol = symbolProvider.toSymbol(output);
                    writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(output.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(output));
                        writer.write("""
                                             func $L(nativeOutput $L)($L) {
                                                 ${C|}
                                             }""", outputToDafnyMethodName,
                                     SmithyNameResolver.getSmithyType(output, outputSymbol),
                                     DafnyNameResolver.getDafnyType(output, outputSymbol),
                                     writer.consumer(w -> generateResponseSerializer(context, operation, context.writerDelegator())));
                    });
                }
            }
        });

        final var refResources = context.model().getShapesWithTrait(ReferenceTrait.class);
        for (var refResource : refResources) {
            final var resource = refResource.expectTrait(ReferenceTrait.class).getReferentId();
            if (!refResource.expectTrait(ReferenceTrait.class).isService()) {
                var resourceShape = model.expectShape(resource, ResourceShape.class);
                resourceShape.getOperations().forEach(eachOperation -> {
                    final var operation = model.expectShape(eachOperation, OperationShape.class);
                    final var input = model.expectShape(operation.getInputShape());
                    if (!alreadyVisited.contains(input.toShapeId())) {
                        alreadyVisited.add(input.toShapeId());
                        if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                            final var inputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, input, "");
                            final var inputSymbol = symbolProvider.toSymbol(input);
                            writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(input.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(input));
                                writer.write("""
                                                     func $L(nativeInput $L)($L) {
                                                         ${C|}
                                                     }""", inputToDafnyMethodName, SmithyNameResolver.getSmithyType(input, inputSymbol),
                                             DafnyNameResolver.getDafnyType(input, inputSymbol),
                                             writer.consumer(w -> generateRequestSerializer(context, operation, context.writerDelegator())));
                            });
                        }
                    }

                    final var output = model.expectShape(operation.getOutputShape());
                    if (!alreadyVisited.contains(output.toShapeId())) {
                        alreadyVisited.add(output.toShapeId());
                        if (!output.hasTrait(UnitTypeTrait.class) && output.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                            final var outputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, output, "");
                            final var outputSymbol = symbolProvider.toSymbol(output);
                            writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(output.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(output));
                                writer.write("""
                                                     func $L(nativeOutput $L)($L) {
                                                         ${C|}
                                                     }""", outputToDafnyMethodName, SmithyNameResolver.getSmithyType(output, outputSymbol),
                                             DafnyNameResolver.getDafnyType(output, outputSymbol),
                                             writer.consumer(w -> generateResponseSerializer(context, operation, context.writerDelegator())));
                            });
                        }
                    }
                    if (!alreadyVisited.contains(resourceShape.toShapeId()) && resourceShape.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                        alreadyVisited.add(resourceShape.toShapeId());
                        writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                            var goBody = """
                                    return nativeResource.(*%s).Impl
                                    """.formatted(resourceShape.getId().getName());
                            if (resourceShape.hasTrait(ExtendableTrait.class)) {
                                goBody = """
                                                                           val, ok := nativeResource.(*%s)
                                        if ok {
                                        	return val.Impl
                                        }
                                        return %s{&NativeWrapper{Impl: nativeResource}}.Impl
                                                                           """.formatted(resourceShape.getId().getName(), resourceShape.getId().getName());
                            }
                            writer.write("""
                                                 func $L_ToDafny(nativeResource $L.I$L) $L.I$L {
                                                     $L
                                                 }
                                                 """, resourceShape.getId().getName(), SmithyNameResolver.smithyTypesNamespace(resourceShape), resourceShape.getId().getName(), DafnyNameResolver.dafnyTypesNamespace(resourceShape), resourceShape.getId().getName(), goBody);
                        });
                    }
                });
            }
        }
        generateErrorSerializer(context);
        if (serviceShape.hasTrait(LocalServiceTrait.class)) {
            generateConfigSerializer(context);
        }
    }

    @Override
    public void generateDeserializers(GenerationContext context) {
        final Set<ShapeId> alreadyVisited = new HashSet<>();
        final var serviceShape = context.settings().getService(context.model());
        final var delegator = context.writerDelegator();

        serviceShape.getOperations().forEach(eachOperation -> {
            var operation = context.model().expectShape(eachOperation, OperationShape.class);

            final var input = context.model().expectShape(operation.getInputShape());
            if (!alreadyVisited.contains(input.toShapeId())) {
                alreadyVisited.add(input.toShapeId());
                if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                    final var inputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, input, "");
                    final var inputSymbol = context.symbolProvider().toSymbol(input);
                    delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(input.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(input));

                        writer.write("""
                                             func $L(dafnyInput $L)($L) {
                                                 ${C|}
                                             }""", inputFromDafnyMethodName, DafnyNameResolver.getDafnyType(input, inputSymbol),
                                     SmithyNameResolver.getSmithyType(input, inputSymbol),
                                     writer.consumer(w -> generateRequestDeserializer(context, operation, context.writerDelegator())));
                    });
                }
            }

            final var output = context.model().expectShape(operation.getOutputShape());
            if (!alreadyVisited.contains(output.toShapeId())) {
                alreadyVisited.add(output.toShapeId());
                if (!output.hasTrait(UnitTypeTrait.class) && output.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                    final var outputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, output, "");
                    final var outputSymbol = context.symbolProvider().toSymbol(output);

                    delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(output.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(output));

                        writer.write("""
                                             func $L(dafnyOutput $L)($L) {
                                                 ${C|}
                                             }""", outputFromDafnyMethodName, DafnyNameResolver.getDafnyType(output, outputSymbol),
                                     SmithyNameResolver.getSmithyType(output, outputSymbol),
                                     writer.consumer(w -> generateResponseDeserializer(context, operation, context.writerDelegator())));
                    });
                }
            }
        });

        var refResources = context.model().getShapesWithTrait(ReferenceTrait.class);
        for (var refResource : refResources) {
            final var resource = refResource.expectTrait(ReferenceTrait.class).getReferentId();

            if (!refResource.expectTrait(ReferenceTrait.class).isService()) {
                var resourceShape = context.model().expectShape(resource, ResourceShape.class);
                resourceShape.getOperations().forEach(eachOperation -> {
                    final var operation = context.model().expectShape(eachOperation, OperationShape.class);
                    final var input = context.model().expectShape(operation.getInputShape());
                    if (!alreadyVisited.contains(input.toShapeId())) {
                        alreadyVisited.add(input.toShapeId());
                        if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                            final var inputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, input, "");
                            final var inputSymbol = context.symbolProvider().toSymbol(input);

                            delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(input.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(input));

                                writer.write("""
                                                     func $L(dafnyInput $L)($L) {
                                                         ${C|}
                                                     }""", inputFromDafnyMethodName, DafnyNameResolver.getDafnyType(input, inputSymbol),
                                             SmithyNameResolver.getSmithyType(input, inputSymbol),
                                             writer.consumer(w -> generateRequestDeserializer(context, operation, context.writerDelegator())));
                            });
                        }
                    }

                    final var output = context.model().expectShape(operation.getOutputShape());
                    if (!alreadyVisited.contains(output.toShapeId())) {
                        alreadyVisited.add(output.toShapeId());
                        if (!output.hasTrait(UnitTypeTrait.class) && output.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                            final var outputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, output, "");
                            final var outputSymbol = context.symbolProvider().toSymbol(output);

                            delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(output.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(output));

                                writer.write("""
                                                     func $L(dafnyOutput $L)($L) {
                                                         ${C|}
                                                     }""", outputFromDafnyMethodName, DafnyNameResolver.getDafnyType(output, outputSymbol),
                                             SmithyNameResolver.getSmithyType(output, outputSymbol),
                                             writer.consumer(w -> generateResponseDeserializer(context, operation, context.writerDelegator())));
                            });
                        }
                    }
                    if (!alreadyVisited.contains(resourceShape.toShapeId()) && resourceShape.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                        alreadyVisited.add(resourceShape.toShapeId());
                        delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                            var extendableResourceWrapperCheck = "";
                            if (resourceShape.hasTrait(ExtendableTrait.class)) {
                                extendableResourceWrapperCheck = """
                                        val, ok := dafnyResource.(*NativeWrapper)
                                        if ok {
                                            return val.Impl
                                        }
                                        """;
                            }
                            writer.write("""
                                                 func $L_FromDafny(dafnyResource $L.I$L)($L.I$L) {
                                                     $L
                                                     return &$L{dafnyResource}
                                                 }
                                                 """, resourceShape.getId().getName(), DafnyNameResolver.dafnyTypesNamespace(resourceShape), resourceShape.getId().getName(), SmithyNameResolver.smithyTypesNamespace(resourceShape), resourceShape.getId().getName(), extendableResourceWrapperCheck, resourceShape.getId().getName());
                        });
                    }

                });
            }
        }
        generateErrorDeserializer(context);
        if (serviceShape.hasTrait(LocalServiceTrait.class)) {
            generateConfigDeserializer(context);
        }

    }

    private void generateRequestSerializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        final var targetShape = context.model().expectShape(operation.getInputShape());
        delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_DAFNY), SmithyNameResolver.shapeNamespace(operation), writer -> {
                                    final var input = targetShape.accept(new SmithyToDafnyShapeVisitor(
                                            context,
                                            "nativeInput",
                                            writer,
                                            false, false, false
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
        delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_DAFNY), SmithyNameResolver.shapeNamespace(operation), writer -> {
                                    final var input = targetShape.accept(new SmithyToDafnyShapeVisitor(
                                            context,
                                            "nativeOutput",
                                            writer,
                                            false, false, false
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
        delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_NATIVE), SmithyNameResolver.shapeNamespace(operation), writer -> {

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
        delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(operation), TO_NATIVE), SmithyNameResolver.shapeNamespace(operation), writer -> {

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
        final var localServiceTrait = service.expectTrait(LocalServiceTrait.class);
        final var configShape = context.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);
        final var getInputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(service, configShape, "");

        context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(service), TO_DAFNY), SmithyNameResolver.shapeNamespace(service), writer -> {
            writer.write("""
                                 func $L(nativeInput $L)($L) {
                                     ${C|}
                                 }""",
                         getInputToDafnyMethodName, SmithyNameResolver.getSmithyType(configShape, context.symbolProvider().toSymbol(configShape)), DafnyNameResolver.getDafnyType(configShape, context.symbolProvider().toSymbol(configShape)),
                         writer.consumer(w -> {
                             String output = configShape.accept(new SmithyToDafnyShapeVisitor(
                                     context,
                                     "nativeInput",
                                     writer,
                                     true, false, false
                             ));
                             writer.write("""
                                                  return $L
                                                  """, output);
                         }));
        });
    }

    private void generateErrorSerializer(final GenerationContext context) {
        final Set<ShapeId> alreadyVisited = new HashSet<>();
        final var serviceShape = context.settings().getService(context.model());
        final var errorShapes = context.model().getShapesWithTrait(ErrorTrait.class);

        for (final var errorShape :
                errorShapes) {
            if (!errorShape.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                continue;
            }
            if (!alreadyVisited.contains(errorShape.toShapeId())) {
                alreadyVisited.add(errorShape.toShapeId());
                final var getInputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, errorShape, "");

                context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(errorShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(errorShape), writer -> {
                    writer.write("""
                                         func $L(nativeInput $L)($L) {
                                             ${C|}
                                         }""",
                                 getInputToDafnyMethodName, SmithyNameResolver.getSmithyType(errorShape, context.symbolProvider().toSymbol(errorShape)), DafnyNameResolver.getDafnyBaseErrorType(errorShape),
                                 writer.consumer(w -> {
                                     String output = errorShape.accept(new SmithyToDafnyShapeVisitor(
                                             context,
                                             "nativeInput",
                                             writer,
                                             false, false, false
                                     ));
                                     writer.write("""
                                                          return $L
                                                          """, output);
                                 }));
                });
            }
        }

        context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
            writer.write("""
                                 func CollectionOfErrors_Input_ToDafny(nativeInput $L.CollectionOfErrors)($L.Error) {
                                 	var e []interface{}
                                 	for _, i2 := range nativeInput.ListOfErrors {
                                        e = append(e, Error_ToDafny(i2))
                                 	}
                                 	return $L.Companion_Error_.Create_CollectionOfErrors_(dafny.SeqOf(e...), dafny.SeqOfChars([]dafny.Char(nativeInput.Message)...))
                                 }
                                 func OpaqueError_Input_ToDafny(nativeInput $L.OpaqueError)($L.Error) {
                                 	return $L.Companion_Error_.Create_Opaque_(nativeInput.ErrObject)
                                 }""", SmithyNameResolver.smithyTypesNamespace(serviceShape),
                         DafnyNameResolver.dafnyTypesNamespace(serviceShape),
                         DafnyNameResolver.dafnyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape), DafnyNameResolver.dafnyTypesNamespace(serviceShape), DafnyNameResolver.dafnyTypesNamespace(serviceShape));
        });


        context.writerDelegator()
               .useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), TO_DAFNY),
                              SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), writer -> {
                           writer.write("""
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
                                                        // TODO: Is changing from the commented code to this new one reasonable?
                                                        // return OpaqueError_Input_ToDafny(err.(*simpleconstraintstypes.OpaqueError))

                                                        // TODO: why is err a pointer?
                                                        error, ok := err.(*$L.OpaqueError)

                                                        if !ok {
                                                            panic("Error is not an OpaqueError")
                                                        }
                                                        if error == nil {
                                                            panic("Error is nil")
                                                        }
                                                        return OpaqueError_Input_ToDafny(*error)
                                                    }
                                                }
                                                """, DafnyNameResolver.dafnyTypesNamespace(serviceShape),
                                        writer.consumer(w -> {
                                            for (var error : serviceShape.getErrors()) {
                                                w.write("""
                                                                  case $L:
                                                                      return $L(err.($L))
                                                                """, SmithyNameResolver.getSmithyType(context.model().expectShape(error), context.symbolProvider().toSymbol(context.model().expectShape(error))),
                                                        SmithyNameResolver.getToDafnyMethodName(serviceShape, context.model().expectShape(error), ""),
                                                        SmithyNameResolver.getSmithyType(context.model().expectShape(error), context.symbolProvider().toSymbol(context.model().expectShape(error))));
                                            }
                                        }),
                                        writer.consumer(w -> {
                                            var dependencies = serviceShape.hasTrait(LocalServiceTrait.class) ? serviceShape.expectTrait(LocalServiceTrait.class).getDependencies() : new LinkedList<ShapeId>();
                                            if (dependencies != null) {
                                                for (var dep : dependencies) {
                                                    var depShape = context.model().expectShape(dep);
                                                    w.write("""
                                                                    case $L.$LBaseException:
                                                                        return $L.Create_$L_($L.Error_ToDafny(err))
                                                                    """, SmithyNameResolver.smithyTypesNamespace(depShape), dep.getName(), DafnyNameResolver.getDafnyErrorCompanion(serviceShape), dep.getName(), SmithyNameResolver.shapeNamespace(depShape));
                                                }
                                            }
                                        }),
                                        SmithyNameResolver.smithyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape)
                           );
                       });
    }

    private void generateConfigDeserializer(final GenerationContext context) {
        final var serviceShape = context.settings().getService(context.model());
        final var localServiceTrait = serviceShape.expectTrait(LocalServiceTrait.class);
        final var configShape = context.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);
        final var getOutputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, configShape, "");

        context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(configShape), writer -> {
            writer.write("""
                                 func $L(dafnyOutput $L)($L) {
                                     ${C|}
                                 }""",
                         getOutputFromDafnyMethodName, DafnyNameResolver.getDafnyType(configShape, context.symbolProvider().toSymbol(configShape)), SmithyNameResolver.getSmithyType(configShape, context.symbolProvider().toSymbol(configShape)),
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
        final Set<ShapeId> alreadyVisited = new HashSet<>();
        final var serviceShape = context.settings().getService(context.model());
        final var errorShapes = context.model().getShapesWithTrait(ErrorTrait.class);
        for (final var errorShape :
                errorShapes) {
            if (!errorShape.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                continue;
            }
            if (!alreadyVisited.contains(errorShape.toShapeId())) {
                alreadyVisited.add(errorShape.toShapeId());
                final var getOutputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, errorShape, "");
                context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(errorShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(errorShape), writer -> {
                    writer.write("""
                                         func $L(dafnyOutput $L)($L) {
                                             ${C|}
                                         }""",
                                 getOutputFromDafnyMethodName, DafnyNameResolver.getDafnyBaseErrorType(errorShape), SmithyNameResolver.getSmithyType(errorShape, context.symbolProvider().toSymbol(errorShape)),
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

        context.writerDelegator().useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), TO_NATIVE), SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), writer -> {
            writer.write("""
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
                                 }""", DafnyNameResolver.dafnyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape),
                         SmithyNameResolver.smithyTypesNamespace(serviceShape),
                         DafnyNameResolver.dafnyTypesNamespace(serviceShape), DafnyNameResolver.dafnyTypesNamespace(serviceShape),
                         SmithyNameResolver.smithyTypesNamespace(serviceShape),
                         SmithyNameResolver.smithyTypesNamespace(serviceShape));
        });

        context.writerDelegator()
               .useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), TO_NATIVE),
                              SmithyNameResolver.shapeNamespace(context.settings().getService(context.model())), writer -> {
                           writer.write("""
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
                                                """, DafnyNameResolver.dafnyTypesNamespace(serviceShape),
                                        writer.consumer(w -> {
                                            for (var error : serviceShape.getErrors()) {
                                                w.write("""
                                                                if err.Is_$L() {
                                                                    return $L(err)
                                                                }
                                                                """, error.getName(), SmithyNameResolver.getFromDafnyMethodName(serviceShape, context.model().expectShape(error), ""));
                                            }
                                        }),
                                        writer.consumer(w -> {
                                            var dependencies = serviceShape.hasTrait(LocalServiceTrait.class) ? serviceShape.expectTrait(LocalServiceTrait.class).getDependencies() : null;
                                            if (dependencies == null) {
                                                return;
                                            }
                                            for (var dep : dependencies) {
                                                var depService = context.model().expectShape(dep, ServiceShape.class);
                                                w.write("""
                                                                if err.Is_$L() {
                                                                    return $L.Error_FromDafny(err.Dtor_$L())
                                                                }
                                                                """, depService.expectTrait(LocalServiceTrait.class).getSdkId(), SmithyNameResolver.shapeNamespace(depService), depService.expectTrait(LocalServiceTrait.class).getSdkId());
                                            }
                                        })
                           );
               });
    }
}
