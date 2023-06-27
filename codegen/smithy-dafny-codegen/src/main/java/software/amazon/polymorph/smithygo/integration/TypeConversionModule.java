// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo.integration;

import software.amazon.polymorph.smithygo.GoCodegenContext;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;

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
                generateMemberWrappers(codegenContext, symbolProvider, memberShape, service);
            });
            generateInputWrappers(codegenContext, symbolProvider, inputShape, service);
            Shape outputShape = model.expectShape(operation.getOutputShape());
            generateOutputWrappers(codegenContext, symbolProvider, outputShape, service);
            codegenContext.writerDelegator().useFileWriter("./typeconversion/typeconversion.go",
                                                           writer -> writer.addImport(String.format("%s%s", service.toShapeId()
                                                                                                                   .getNamespace()
                                                                                                                   .replace(".", ""), "internaldafnytypes"),
                                                                                      ""));
            codegenContext.writerDelegator().useFileWriter("./typeconversion/typeconversion.go",
                                                           writer -> writer.addImport( "types", ""));
        }
    }

    private void generateInputWrappers(final GoCodegenContext codegenContext, final SymbolProvider symbolProvider, final Shape inputShape, final Shape service) {
        codegenContext.writerDelegator().useFileWriter("./typeconversion/typeconversion.go", goWriter -> {
                                                           goWriter.write("func FromDafnyToNative$L(val $L) ($T, error) {",
                                                                          symbolProvider.toSymbol(inputShape).getName(),
                                                                          String.format("%s%s%s", service.toShapeId()
                                                                                                         .getNamespace()
                                                                                                         .replace(".", ""),
                                                                                        "internaldafnytypes.",
                                                                                        symbolProvider.toSymbol(inputShape).getName()),
                                                                          symbolProvider.toSymbol(inputShape));
                                                           goWriter.write("""
                                                                                       var r, err = FromDafnyToNativebool(val.Dtor_value())
                                                                                       return types.GetBooleanInput{Value: r}, err
                                                                                       """);
                                                           goWriter.write("}");

                                                           goWriter.write("func FromNativeToDafny$L(val $T) ($L, error) {",
                                                                          symbolProvider.toSymbol(inputShape).getName(),
                                                                          symbolProvider.toSymbol(inputShape),
                                                                          String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""),
                                                                                        "internaldafnytypes.", symbolProvider.toSymbol(inputShape).getName()));
                                                           goWriter.write("""
                                                                                       var r, err = FromNativeToDafnybool(val.Value)
                                                                                       return simpletypesbooleaninternaldafnytypes.Companion_GetBooleanInput_.Create_GetBooleanInput_(r), err
                                                                                       """);
                                                           goWriter.write("}");
                                                       }
        );
    }

    private void generateOutputWrappers(final GoCodegenContext codegenContext, final SymbolProvider symbolProvider, final Shape outputShape, final Shape service) {
        codegenContext.writerDelegator().useFileWriter("./typeconversion/typeconversion.go", goWriter -> {
                                                           goWriter.write("func FromDafnyToNative$L(val $L) ($T, error) {",
                                                                          symbolProvider.toSymbol(outputShape).getName(),
                                                                          String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""),
                                                                                        "internaldafnytypes.", symbolProvider.toSymbol(outputShape).getName()),
                                                                          symbolProvider.toSymbol(outputShape));
                                                           goWriter.write("""
                                                                                       var r, err = FromDafnyToNativebool(val.Dtor_value())
                                                                                       return types.GetBooleanOutput{Value: r}, err
                                                                                       """);
                                                           goWriter.write("}");

                                                           goWriter.write("func FromNativeToDafny$L(val $T) ($L, error) {",
                                                                          symbolProvider.toSymbol(outputShape).getName(),
                                                                          symbolProvider.toSymbol(outputShape),
                                                                          String.format("%s%s%s", service.toShapeId().getNamespace().replace(".", ""),
                                                                                        "internaldafnytypes.", symbolProvider.toSymbol(outputShape).getName()));
                                                           goWriter.write("""
                                                                                       var r, err = FromNativeToDafnybool(val.Value)
                                                                                       return simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Create_GetBooleanOutput_(r), err
                                                                                       """);
                                                           goWriter.write("}");
                                                       }
        );
    }

    private void generateMemberWrappers(final GoCodegenContext codegenContext, final SymbolProvider symbolProvider, final Shape memberShape, final Shape service) {
        codegenContext.writerDelegator().useShapeWriter(memberShape, goWriter -> {
                                                            symbolProvider.toSymbol(memberShape).getProperty("dafny", Symbol.class)
                                                                          .get().getDependencies().stream()
                                                                          .forEach(depenmdency -> goWriter.addImport(depenmdency.getPackageName(), depenmdency.getVersion()));
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
    }
}
