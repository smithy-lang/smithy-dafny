package software.amazon.polymorph.smithygo.integration;

import software.amazon.polymorph.smithygo.GoCodegenContext;
import software.amazon.polymorph.smithygo.SmithyGoDependency;
import software.amazon.polymorph.smithygo.StructureGenerator;
import software.amazon.polymorph.smithygo.SymbolUtils;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import java.util.Set;
import java.util.TreeSet;

public class TypeConversionModule implements GoIntegration {
    @Override
    public void customize(GoCodegenContext codegenContext) {
        Model model = codegenContext.model();
        Shape service = codegenContext.settings().getService(model);
        TopDownIndex topDownIndex = model.getKnowledge(TopDownIndex.class);
        Set<OperationShape> containedOperations = new TreeSet<>(topDownIndex.getContainedOperations(service.toShapeId()));
        SymbolProvider symbolProvider = codegenContext.symbolProvider();
        for (OperationShape operation : containedOperations) {
            Shape inputShape = model.expectShape(operation.getInputShape());
            inputShape.asStructureShape().get().members().forEach(memberShape -> {

                codegenContext.writerDelegator().useShapeWriter(memberShape, goWriter -> {
                                                                    symbolProvider.toSymbol(memberShape).getProperty("dafny", Symbol.class).get().getDependencies().stream().forEach(depenmdency -> goWriter.addImport(depenmdency.getPackageName(), depenmdency.getVersion()));
                                                                    goWriter.write("func FromDafnyToNative$T(val $T) ($T, error) {",
                                                                                   symbolProvider.toSymbol(memberShape),
                                                                                   symbolProvider.toSymbol(memberShape).getProperty("dafny", Symbol.class).get(),
                                                                                   symbolProvider.toSymbol(memberShape).getProperty("native", Symbol.class).get());
                                                                    goWriter.write("return $L, nil", symbolProvider.toSymbol(memberShape).getProperty("ToNative", String.class).get());
                                                                    goWriter.write("}");

                                                                    goWriter.write("func FromNativeToDafny$T(val $T) ($T, error) {",
                                                                                   symbolProvider.toSymbol(memberShape),
                                                                                   symbolProvider.toSymbol(memberShape).getProperty("native", Symbol.class).get(),
                                                                                   symbolProvider.toSymbol(memberShape).getProperty("dafny", Symbol.class).get());
                                                                    goWriter.write("return $L, nil", symbolProvider.toSymbol(memberShape).getProperty("ToDafny", String.class).get());
                                                                    goWriter.write("}");
                                                                }
                );
            });

            codegenContext.writerDelegator().useFileWriter("TypeConversion.go", goWriter -> {
                goWriter.write("func FromDafnyToNative$L(val $L) ($T, error) {",
                                                                               symbolProvider.toSymbol(inputShape).getName(),
                                                                               String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""), "internaldafnytypes.", symbolProvider.toSymbol(inputShape).getName()),
                                                                               symbolProvider.toSymbol(inputShape));
                                                                goWriter.write("""
                                                                                       var r, err = FromDafnyToNativebool(val.Dtor_value())
                                                                                       return types.GetBooleanInput{Value: r}, err
                                                                                       """);
                                                                goWriter.write("}");

                                                                goWriter.write("func FromNativeToDafny$L(val $T) ($L, error) {",
                                                                               symbolProvider.toSymbol(inputShape).getName(),
                                                                               symbolProvider.toSymbol(inputShape),
                                                                               String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""), "internaldafnytypes.", symbolProvider.toSymbol(inputShape).getName()));
                                                                goWriter.write("""
                                                                                       var r, err = FromNativeToDafnybool(val.Value)
                                                                                       return simpletypesbooleaninternaldafnytypes.Companion_GetBooleanInput_.Create_GetBooleanInput_(r), err
                                                                                       """);
                                                                goWriter.write("}");
                                                            }
            );

            Shape outputShape = model.expectShape(operation.getOutputShape());

            codegenContext.writerDelegator().useFileWriter("TypeConversion.go", goWriter -> {
                                                                goWriter.write("func FromDafnyToNative$L(val $L) ($T, error) {",
                                                                               symbolProvider.toSymbol(outputShape).getName(),
                                                                               String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""), "internaldafnytypes.", symbolProvider.toSymbol(outputShape).getName()),
                                                                               symbolProvider.toSymbol(outputShape));
                                                                goWriter.write("""
                                                                                       var r, err = FromDafnyToNativebool(val.Dtor_value())
                                                                                       return types.GetBooleanOutput{Value: r}, err
                                                                                       """);
                                                                goWriter.write("}");

                                                                goWriter.write("func FromNativeToDafny$L(val $T) ($L, error) {",
                                                                               symbolProvider.toSymbol(outputShape).getName(),
                                                                               symbolProvider.toSymbol(outputShape),
                                                                               String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""), "internaldafnytypes.", symbolProvider.toSymbol(outputShape).getName()));
                                                                goWriter.write("""
                                                                                       var r, err = FromNativeToDafnybool(val.Value)
                                                                                       return simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Create_GetBooleanOutput_(r), err
                                                                                       """);
                                                                goWriter.write("}");
                                                            }
            );
            codegenContext.writerDelegator().useFileWriter("TypeConversion.go", writer -> writer.addImport( String.format("%s%s", service.toShapeId().getNamespace().replace(".", ""), "internaldafnytypes"), ""));
            codegenContext.writerDelegator().useFileWriter("TypeConversion.go", writer -> writer.addImport( "types", ""));
        }
    }
}
