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
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.ToShapeId;

import static software.amazon.polymorph.smithygo.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.nameresolver.Constants.DOT;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getFromDafnyMethodName;
import static software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver.getToDafnyMethodName;

public class DafnyTypeConversionProtocol implements ProtocolGenerator {
    public static String TO_DAFNY = "to_dafny.go";
    public static String FROM_DAFNY = "from_dafny.go";

    @Override
    public ShapeId getProtocol() {
        return null;
    }

    @Override
    public ApplicationProtocol getApplicationProtocol() {
        return null;
    }

    @Override
    public void generateRequestSerializers(GenerationContext context) {
        final var model = context.model();
        final var serviceShape = model.expectShape(context.settings().getService(), ServiceShape.class);
        final var symbolProvider = context.symbolProvider();
        final var writerDelegator = context.writerDelegator();
        final var topDownIndex = TopDownIndex.of(model);
        for (final var operation : topDownIndex.getContainedOperations(serviceShape)) {
            final var toDafnyMethodName = getToDafnyMethodName(context, operation);
            final var input = model.expectShape(operation.getInputShape());
            final var inputSymbol = symbolProvider.toSymbol(input);
            writerDelegator.useFileWriter(TO_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");
                writer.write("""
                  func $L(input $T)($L) {
                      ${C|}
                  }""", toDafnyMethodName, inputSymbol,
                             DafnyNameResolver.getDafnyType(context.settings(), inputSymbol),
                             writer.consumer(w -> generateRequestSerializer(context, operation, context.writerDelegator())));
            });
        }
        generateConfigSerializer(context);
    }

    @Override
    public void generateResponseDeserializers(GenerationContext context) {
        final var topDownIndex = TopDownIndex.of(context.model());
        final var service = context.settings().getService(context.model());
        final var delegator = context.writerDelegator();

        for (final var operation : topDownIndex.getContainedOperations(service)) {

            final var deserFunction = getFromDafnyMethodName(context, operation);
            final var output = context.model().expectShape(operation.getOutputShape());
            final var outputSymbol = context.symbolProvider().toSymbol(output);

            delegator.useFileWriter(FROM_DAFNY, context.settings().getModuleName().replace(DOT, BLANK).toLowerCase(), writer -> {
                writer.addImport("types");

                writer.write("""
                  func $L(input $L)($T) {
                      ${C|}
                  }""", deserFunction, DafnyNameResolver.getDafnyType(context.settings(), outputSymbol),
                             outputSymbol,
                             writer.consumer(w -> generateOperationResponseDeserializer(context, operation, context.writerDelegator())));
            });
        }

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
                                                            "input",
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

    private void generateOperationResponseDeserializer(
            final GenerationContext context,
            final OperationShape operation,
            final GoDelegator delegator
    ) {
        delegator.useFileWriter(FROM_DAFNY, writer -> {

            final var outputShape = operation.getOutputShape();

            final var targetShape = context.model().expectShape(outputShape);
            final var output = targetShape.accept(new DafnyToSmithyShapeVisitor(
                    context,
                    "input.Dtor_value()",
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

        String moduleName = context.settings().getModuleName();
        context.writerDelegator().useFileWriter(TO_DAFNY, writer -> {
            writer.write("""
                  func $L(input $T)($L) {
                      ${C|}
                  }""",
        getToDafnyMethodName(context, configShape), context.symbolProvider().toSymbol(configShape), DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(configShape)),
        writer.consumer( w -> {
            String output = configShape.accept(new SmithyToDafnyShapeVisitor(
                    context,
                    "smithy_config",
                    writer,
                    true
            ));
            writer.write("""
                                 return $L
                                 """, output);
        }));
    });
    }

    private void generateConfigDeserializer(final GenerationContext context) {
        final var service = context.settings().getService(context.model());
        final LocalServiceTrait localServiceTrait = service.expectTrait(LocalServiceTrait.class);
        final StructureShape configShape = context.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);

        String moduleName = context.settings().getModuleName();
        context.writerDelegator().useFileWriter(FROM_DAFNY, writer -> {
            writer.write("""
                  func $L(input $L)($T) {
                      ${C|}
                  }""",
                         getFromDafnyMethodName(context, configShape), DafnyNameResolver.getDafnyType(context.settings(), context.symbolProvider().toSymbol(configShape)), context.symbolProvider().toSymbol(configShape),
                         writer.consumer( w -> {
                             String output = configShape.accept(new DafnyToSmithyShapeVisitor(
                                     context,
                                     "smithy_config",
                                     writer,
                                     true
                             ));
                             writer.write("""
                                 return $L
                                 """, output);
                         }));
        });
    }


}
