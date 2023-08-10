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

package software.amazon.polymorph.smithypython;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.customize.ConfigFileWriter;
import software.amazon.polymorph.smithypython.customize.DafnyImplInterfaceFileWriter;
import software.amazon.polymorph.smithypython.customize.DafnyProtocolFileWriter;
import software.amazon.polymorph.smithypython.customize.ErrorsFileWriter;
import software.amazon.polymorph.smithypython.customize.ModelsFileWriter;
import software.amazon.polymorph.smithypython.customize.PluginFileWriter;
import software.amazon.polymorph.smithypython.customize.ShimFileWriter;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.ConfigField;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.utils.CodeSection;

public final class DafnyPythonIntegration implements PythonIntegration {
    private RuntimeClientPlugin dafnyImplRuntimeClientPlugin = RuntimeClientPlugin.builder()
        .configFields(
            // Adds a new field in the client class' config.
            // This is an interface for the Dafny implementation code.
            // The Smithy-Dafny Python plugin generates a dafnyImplInterface file
            // and populates it with the relevant information from the model
            // to interact with the Dafny implementation.
            // We use an interface as we cannot plug the model into the RuntimeClientPlugin definition,
            // but we can point the RuntimeClientPlugin to an interface and plug the model in there.
            // TODO: Naming of DafnyImplInterface?
            Collections.singletonList(new ConfigField("dafnyImplInterface",
                Symbol.builder()
                    .name("DafnyImplInterface")
                    .namespace(".dafnyImplInterface", ".")
                .build(),
                // isOptional is marked as true here.
                // This allows the Config to be instantiated without providing a plugin.
                // However, this plugin MUST be present before using the client.
                // Immediately after the Config is instantiated, the client will add the plugin.
                true, ""))
         ).pythonPlugin(
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
        Set<ServiceShape> serviceShapes = codegenContext.model().getServiceShapes();

        for (ServiceShape serviceShape : serviceShapes) {
            customizeForServiceShape(serviceShape, codegenContext);
        }
    }

    private void customizeForServiceShape(ServiceShape serviceShape, GenerationContext codegenContext) {
        new PluginFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new DafnyImplInterfaceFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new DafnyProtocolFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new ShimFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new ErrorsFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new ModelsFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
        new ConfigFileWriter().generateFileForServiceShape(serviceShape, codegenContext);
    }

    /**
     * Creates the Dafny ApplicationProtocol object.
     * At the moment, this is entirely unused boilerplate.
     * Smithy-Python requires this boilerplate, but the Dafny plugin doesn't use it.
     *
     * @return Returns the created application protocol.
     */
    public static ApplicationProtocol createDafnyApplicationProtocol() {
        return new ApplicationProtocol(
            "dafny",
            // TODO: Naming of these symbols?
            // TODO: This is just the input/output of a Dafny call, right?
            //       If that is true, is output just Wrappers.result?
            //       Then what is input? Maybe DafnyCallEvent?
            // Input: Not DafnyCallEvent. There is no Dafny-generated type for input.
            // Input can be the corresponding Dafny class for any of the operation input shapes,
            // Dafny does not generate some superclass relating these.
            // If we want to specify this, we must specify it in dafny_protocol.py.
            // It will look like
            // DafnyInput = Tuple(
            //     String,
            //     Union[forall operations in service: operation.getInputShape()]
            // )
            // Output: This is the value returned from the client calling dafnyImplInterface.
            // I believe this is a Wrappers.Result, which I should use.
            SymbolReference.builder()
                .symbol(createDafnySymbol("DafnyRequest"))
                .build(),
            SymbolReference.builder()
                .symbol(createDafnySymbol("DafnyResponse"))
                .build()
        );
    }

    private static Symbol createDafnySymbol(String symbolName) {
        return Symbol.builder()
            .namespace(".dafny_protocol", ".")
            .name(symbolName)
            .build();
    }

    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {
        return Collections.singletonList(new DafnyPythonProtocolGenerator() {
            @Override
            protected void generateDocumentBodyShapeDeserializers(GenerationContext context,
                Set<Shape> shapes) {
                // Do nothing
            }

            @Override
            public ShapeId getProtocol() {
                return ShapeId.from("aws.polymorph#localService");
            }
        });
    }

    @Override
    public List<RuntimeClientPlugin> getClientPlugins() {
        return Collections.singletonList(dafnyImplRuntimeClientPlugin);
    }
}
