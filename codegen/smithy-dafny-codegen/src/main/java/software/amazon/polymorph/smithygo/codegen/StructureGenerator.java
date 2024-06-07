/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.polymorph.smithygo.codegen;

import software.amazon.polymorph.smithygo.codegen.integration.ProtocolGenerator;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.StreamingTrait;
import software.amazon.smithy.utils.SetUtils;

import java.util.Set;

/**
 * Renders structures.
 */
public final class StructureGenerator implements Runnable {
    private static final Set<String> ERROR_MEMBER_NAMES = SetUtils.of("ErrorMessage", "Message", "ErrorCodeOverride");

    private final Model model;
    private final SymbolProvider symbolProvider;
    private final GoWriter writer;
    private final StructureShape shape;

    public StructureGenerator(
            Model model,
            SymbolProvider symbolProvider,
            GoWriter writer,
            StructureShape shape) {
        this.model = model;
        this.symbolProvider = symbolProvider;
        this.writer = writer;
        this.shape = shape;
    }

    @Override
    public void run() {
        if (!shape.hasTrait(ErrorTrait.class)) {
            renderStructure(() -> {
            });
        } else {
            renderErrorStructure();
        }
    }

    /**
     * Renders a non-error structure.
     *
     * @param runnable A runnable that runs before the structure definition is closed. This can be used to write
     *                 additional members.
     */
    public void renderStructure(Runnable runnable) {
        renderStructure(runnable, false);
    }

    /**
     * Renders a non-error structure.
     *
     * @param runnable         A runnable that runs before the structure definition is closed. This can be used to write
     *                         additional members.
     * @param isInputStructure A boolean indicating if input variants for member symbols should be used.
     */
    public void renderStructure(Runnable runnable, boolean isInputStructure) {
        Symbol symbol = symbolProvider.toSymbol(shape);
        writer.openBlock("type $L struct {", symbol.getName());

        CodegenUtils.SortedMembers sortedMembers = new CodegenUtils.SortedMembers(symbolProvider);
        shape.getAllMembers().values().stream()
                .filter(memberShape -> !StreamingTrait.isEventStream(model, memberShape))
                .sorted(sortedMembers)
                .forEach((member) -> {
                    writer.write("");

                    String memberName = symbolProvider.toMemberName(member);

                    Symbol memberSymbol = symbolProvider.toSymbol(member);
                    if (isInputStructure) {
                        memberSymbol = memberSymbol.getProperty(SymbolUtils.INPUT_VARIANT, Symbol.class)
                                .orElse(memberSymbol);
                    }

                    if (model.expectShape(member.getTarget()).hasTrait(ReferenceTrait.class)) {
                        memberSymbol = memberSymbol.getProperty("Referred", Symbol.class).get();
                    }

                    writer.write("$L $P", memberName, memberSymbol);
                });


        writer.closeBlock("}").write("");

        writer.openBlock("func (input $L) Validate() (error) {", symbol.getName());
        shape.getAllMembers().values().stream()
                .filter(memberShape -> !StreamingTrait.isEventStream(model, memberShape))
                .sorted(sortedMembers)
                .forEach((member) -> {
                    String memberName = symbolProvider.toMemberName(member);

                    Symbol memberSymbol = symbolProvider.toSymbol(member);

                    
                    writer.write("$L $P", memberName, memberSymbol);
                });
        writer.closeBlock("}").write("");
    }

    /**
     * Renders an error structure and supporting methods.
     */
    private void renderErrorStructure() {
            Symbol structureSymbol = symbolProvider.toSymbol(shape);
            writer.addUseImports(SmithyGoDependency.FMT);
            ErrorTrait errorTrait = shape.expectTrait(ErrorTrait.class);

            // Write out a struct to hold the error data.
            writer.openBlock("type $L struct {", "}", structureSymbol.getName(), () -> {
                // The message is the only part of the standard APIError interface that isn't known ahead of time.
                // Message is a pointer mostly for the sake of consistency.
                writer.write("Message *string").write("");
                writer.write("ErrorCodeOverride *string").write("");

                for (MemberShape member : shape.getAllMembers().values()) {
                    String memberName = symbolProvider.toMemberName(member);
                    // error messages are represented under Message for consistency
                    if (!ERROR_MEMBER_NAMES.contains(memberName)) {
                        writer.write("$L $P", memberName, symbolProvider.toSymbol(member));
                    }
                }

            }).write("");

            // write the Error method to satisfy the standard error interface
            writer.openBlock("func (e $L) Error() string {", "}", structureSymbol.getName(), () -> {
                writer.write("return fmt.Sprintf(\"%s: %s\", e.ErrorCodeOverride, e.Message)");
            });
    }
}
