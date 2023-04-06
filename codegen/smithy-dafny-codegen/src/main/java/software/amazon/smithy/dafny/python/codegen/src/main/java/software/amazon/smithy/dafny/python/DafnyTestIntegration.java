/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *   http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.smithy.dafny.python;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import software.amazon.smithy.codegen.core.ReservedWords;
import software.amazon.smithy.codegen.core.ReservedWordsBuilder;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.ConfigField;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonDependency;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;

public final class DafnyTestIntegration implements
    software.amazon.smithy.python.codegen.integration.PythonIntegration {

    private RuntimeClientPlugin assignDafnyImplRuntimeClientPlugin = RuntimeClientPlugin.builder()
        .configFields(
            Collections.singletonList(new ConfigField("impl",
                Symbol.builder()
                    .name("config_type")
                    .namespace("Path.To.Config.Namespace", ".")
                    .build(),
                false, "")))
        .pythonPlugin(SymbolReference.builder()
            .symbol(Symbol.builder()
                .name("set_config_impl")
                .namespace(".", ".")
                .build())
            .build())
        .build();


    @Override
    public void customize(GenerationContext codegenContext) {
        codegenContext.writerDelegator().useFileWriter("Iamaredme", "", writer -> {
            // The $ character is escaped using $$
            writer.write("yo");
        });
    }

    /**
     * Creates a default HTTP application protocol.
     *
     * @return Returns the created application protocol.
     */
    public static ApplicationProtocol createDafnyApplicationProtocol() {
        return new ApplicationProtocol(
            "dafny",
            SymbolReference.builder()
                .symbol(createHttpSymbol("IaAmDafny"))
                .build(),
            SymbolReference.builder()
                .symbol(createHttpSymbol("IamaAlsoDafny"))
                .build()
        );
    }

    private static Symbol createHttpSymbol(String symbolName) {
        PythonDependency dependency = SmithyPythonDependency.SMITHY_PYTHON;
        return Symbol.builder()
            .namespace(dependency.packageName() + ".interfaces.http", ".")
            .name(symbolName)
            .addDependency(dependency)
            .build();
    }

    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {

        return Collections.singletonList(new DafnyProtocolGenerator() {

            @Override
            protected void generateDocumentBodyShapeDeserializers(GenerationContext context,
                Set<Shape> shapes) {

            }

            @Override
            public ShapeId getProtocol() {
                return ShapeId.from("aws.polymorph#localService");
            }
        });
    }

    @Override
    public List<RuntimeClientPlugin> getClientPlugins() {
        return Collections.singletonList(assignDafnyImplRuntimeClientPlugin);
    }
}
