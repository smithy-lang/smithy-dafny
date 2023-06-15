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
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.utils.CodeSection;

public final class DafnyTestIntegration implements
    software.amazon.smithy.python.codegen.integration.PythonIntegration {

    private RuntimeClientPlugin assignDafnyImplRuntimeClientPlugin = RuntimeClientPlugin.builder()
        .configFields(
            Collections.singletonList(new ConfigField("impl",
                Symbol.builder()
                    // TODO: ISimple..>?
                    .name("ISimpleBooleanClient")
                    .namespace("simple.types.boolean.internaldafny.types", ".")
                    .build(),
                true, ""))
         ).pythonPlugin(
             // TODO: ??????
            // This goes into client_plugins.... I do not think I need to plug in tho?
            // Since IG this is a runtime plugin but idk if we need anything at runtime
             SymbolReference.builder()
             .symbol(
                 Symbol.builder()
                 .name("set_config_impl")
                 .namespace(".plugin", ".")
                 .build())
             .build()
         )
        .build();

    @Override
    public List<? extends CodeInterceptor<? extends CodeSection, PythonWriter>>
    interceptors(GenerationContext codegenContext) {
        return List.of(new SendRequestInterceptor());
    }
    @Override
    public void customize(GenerationContext codegenContext) {
        codegenContext.writerDelegator().useFileWriter("simple_boolean/plugin.py", "", writer -> {
            // The $ character is escaped using $$
            writer.write("""
from .config import Config, Plugin
from smithy_python.interfaces.retries import RetryStrategy
from smithy_python.exceptions import SmithyRetryException

def set_config_impl(config: Config):
    from simple.types.boolean.internaldafny.impl import SimpleBooleanClient
    config.impl = SimpleBooleanClient()
    config.retry_strategy = NoRetriesStrategy()

class NoRetriesToken:
    retry_delay = 0

class NoRetriesStrategy(RetryStrategy):
    def acquire_initial_retry_token(self):
        return NoRetriesToken()

    def refresh_retry_token_for_retry(self, token_to_renew, error_info):
        raise SmithyRetryException()
                                """);
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
                .symbol(createDafnySymbol("GetBooleanOutput_GetBooleanOutput"))
                .build(),
            SymbolReference.builder()
                .symbol(createDafnySymbol("GetBooleanInput_GetBooleanInput"))
                .build()
        );
    }

    private static Symbol createDafnySymbol(String symbolName) {
        // TODO: ?????
        return Symbol.builder()
            .namespace("simple.types.boolean.internaldafny.types", ".")
            .name(symbolName)
//            .addDependency(dependency)
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
