package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.codegen.ApplicationProtocol;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.shapevisitor.SmithyToDafnyShapeVisitor;
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

import java.util.HashSet;
import java.util.Set;

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
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));
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
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));
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
                    model.expectShape(resource, ResourceShape.class).getOperations().forEach(eachOperation -> {
                        final var operation = model.expectShape(eachOperation, OperationShape.class);
                        final var input = model.expectShape(operation.getInputShape());
                        if (!alreadyVisited.contains(input.toShapeId())) {
                            alreadyVisited.add(input.toShapeId());
                            if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                                final var inputToDafnyMethodName = SmithyNameResolver.getToDafnyMethodName(serviceShape, input, "");
                                final var inputSymbol = symbolProvider.toSymbol(input);
                                writerDelegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_DAFNY), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                    writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));
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
                                    writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));
                                    writer.write("""
                                                         func $L(nativeOutput $L)($L) {
                                                             ${C|}
                                                         }""", outputToDafnyMethodName, SmithyNameResolver.getSmithyType(output, outputSymbol),
                                                 DafnyNameResolver.getDafnyType(output, outputSymbol),
                                                 writer.consumer(w -> generateResponseSerializer(context, operation, context.writerDelegator())));
                                });
                            }
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
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));

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
                        writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));

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

                context.model().expectShape(resource, ResourceShape.class).getOperations().forEach(eachOperation -> {
                    final var operation = context.model().expectShape(eachOperation, OperationShape.class);
                    final var input = context.model().expectShape(operation.getInputShape());
                    if (!alreadyVisited.contains(input.toShapeId())) {
                        alreadyVisited.add(input.toShapeId());
                        if (!input.hasTrait(UnitTypeTrait.class) && input.toShapeId().getNamespace().equals(serviceShape.toShapeId().getNamespace())) {
                            final var inputFromDafnyMethodName = SmithyNameResolver.getFromDafnyMethodName(serviceShape, input, "");
                            final var inputSymbol = context.symbolProvider().toSymbol(input);

                            delegator.useFileWriter("%s/%s".formatted(SmithyNameResolver.shapeNamespace(serviceShape), TO_NATIVE), SmithyNameResolver.shapeNamespace(serviceShape), writer -> {
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));

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
                                writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(serviceShape.toShapeId().getNamespace()), SmithyNameResolver.smithyTypesNamespace(serviceShape));

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
	    switch i2.(type) {
            ${C|}
            case $L.CollectionOfErrors:
                e = append(e, CollectionOfErrors_Input_ToDafny(i2.($L.CollectionOfErrors)))
            default:
                e = append(e, OpaqueError_Input_ToDafny(i2.($L.OpaqueError)))
            }
	}
	return $L.Companion_Error_.Create_CollectionOfErrors_(dafny.SeqOf(e...), dafny.SeqOfChars([]dafny.Char(nativeInput.Message)...))
}
func OpaqueError_Input_ToDafny(nativeInput $L.OpaqueError)($L.Error) {
	return $L.Companion_Error_.Create_Opaque_(nativeInput.ErrObject)
}""",             SmithyNameResolver.smithyTypesNamespace(serviceShape),
                DafnyNameResolver.dafnyTypesNamespace(serviceShape), writer.consumer(w -> {
                    for (Shape error:
                            context.model().getShapesWithTrait(ErrorTrait.class)) {
                        w.write("""
                                 case $L.$L:
                                      e = append(e, $L(i2.($L.$L)))
                                 """, SmithyNameResolver.smithyTypesNamespace(serviceShape), context.symbolProvider().toSymbol(error).getName(), SmithyNameResolver.getToDafnyMethodName(serviceShape, error, ""), SmithyNameResolver.smithyTypesNamespace(serviceShape), context.symbolProvider().toSymbol(error).getName());
                    }
                }), SmithyNameResolver.smithyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape),
                        DafnyNameResolver.dafnyTypesNamespace(serviceShape), SmithyNameResolver.smithyTypesNamespace(serviceShape), DafnyNameResolver.dafnyTypesNamespace(serviceShape), DafnyNameResolver.dafnyTypesNamespace(serviceShape));
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
        ${C|}
                                           if err.Is_CollectionOfErrors() {
            t.ListOfErrors = append(t.ListOfErrors, CollectionOfErrors_Output_FromDafny(err))
                                           }
                                           if err.Is_Opaque() {
            t.ListOfErrors = append(t.ListOfErrors, OpaqueError_Output_FromDafny(err))
                                           }
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
                         DafnyNameResolver.dafnyTypesNamespace(serviceShape), writer.consumer( w -> {
                for (var errorShape :
                        context.model().getShapesWithTrait(ErrorTrait.class)) {
                    w.write("""
                                                                             if err.Is_$L() {
                                                                              t.ListOfErrors = append(t.ListOfErrors,  $L(err))
                                                                         }
                                                      """, errorShape.toShapeId().getName(), SmithyNameResolver.getFromDafnyMethodName(serviceShape, errorShape, ""));
                }
            }), DafnyNameResolver.dafnyTypesNamespace(serviceShape),
                         SmithyNameResolver.smithyTypesNamespace(serviceShape),
            SmithyNameResolver.smithyTypesNamespace(serviceShape));
            });
    }
}
