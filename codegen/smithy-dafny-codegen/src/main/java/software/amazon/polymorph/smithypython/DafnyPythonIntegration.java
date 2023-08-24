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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.customize.ConfigFileWriter;
import software.amazon.polymorph.smithypython.customize.DafnyImplInterfaceFileWriter;
import software.amazon.polymorph.smithypython.customize.DafnyProtocolFileWriter;
import software.amazon.polymorph.smithypython.customize.ErrorsFileWriter;
import software.amazon.polymorph.smithypython.customize.ModelsFileWriter;
import software.amazon.polymorph.smithypython.customize.PluginFileWriter;
import software.amazon.polymorph.smithypython.customize.ShimFileWriter;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.ConfigProperty;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.utils.CodeSection;

public final class DafnyPythonIntegration implements PythonIntegration {
    private RuntimeClientPlugin dafnyImplRuntimeClientPlugin = RuntimeClientPlugin.builder()
        .configProperties(
            // Adds a new field in the client class' config.
            // `dafnyImplInterface` is a static interface for accessing Dafny implementation code.
            // The Smithy-Dafny Python plugin generates a dafnyImplInterface file
            //   and populates it with the relevant information from the model
            //   to interact with the Dafny implementation.
            // We use a static interface as we cannot plug the model into this RuntimeClientPlugin definition,
            //   so this class cannot be aware of model shapes.
            // To work around this, we can point the RuntimeClientPlugin to a static interface
            //   that IS aware of model shapes, and plug the model in there.
            // TODO: Naming of DafnyImplInterface?
            Collections.singletonList(ConfigProperty.builder()
                .name("dafnyImplInterface")
                .type(
                    Symbol.builder()
                        .name("DafnyImplInterface")
                        .namespace(".dafnyImplInterface", ".")
                    .build()
                )
                // nullable is marked as true here.
                // This allows the Config to be instantiated without providing a plugin.
                // However, this plugin MUST be present before using the client.
                // Immediately after the Config is instantiated, the client will add the plugin.
                .nullable(true)
                .documentation("")
                .build()
            )
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
        // Generate for service shapes with localService trait
        Set<ServiceShape> serviceShapes = Set.of(
            codegenContext.model().expectShape(codegenContext.settings().getService()).asServiceShape().get());

        ServiceShape serviceShape = codegenContext.model().expectShape(codegenContext.settings().getService()).asServiceShape().get();

        customizeForServiceShape(serviceShape, codegenContext);

        // Get set(non-service operation shapes) = set(model operation shapes) - set(service operation shapes)
        // This is related to forking Smithy-Python. TODO: resolve when resolving fork.
        // Smithy-Python will only generate code for shapes which are used by the service.
        // Polymorph has a requirement to generate code for all shapes in the model,
        //   even if the service does not use those shapes.
        // (The use case is that other models may depend on shapes that are defined in this model,
        //   though not used in this model.)
        Set<ShapeId> serviceOperationShapes = serviceShapes.stream()
            .map(EntityShape::getOperations)
            .flatMap(Collection::stream)
            .collect(Collectors.toSet());
        Set<ShapeId> nonServiceOperationShapes = codegenContext.model().getOperationShapes().stream()
            .map(Shape::getId)
            .filter(operationShapeId -> operationShapeId.getNamespace().equals(serviceShape.getId().getNamespace()))
            .collect(Collectors.toSet());
        nonServiceOperationShapes.removeAll(serviceOperationShapes);

        customizeForNonServiceOperationShapes(nonServiceOperationShapes, codegenContext);
    }

    private void customizeForNonServiceOperationShapes(Set<ShapeId> operationShapeIds, GenerationContext codegenContext) {
        new ModelsFileWriter().customizeFileForNonServiceOperationShapes(operationShapeIds, codegenContext);
    }

    private void customizeForServiceShape(ServiceShape serviceShape, GenerationContext codegenContext) {
        new PluginFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new DafnyImplInterfaceFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new DafnyProtocolFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ShimFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ErrorsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ModelsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ConfigFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
    }

    /**
     * Creates the Dafny ApplicationProtocol object.
     *
     * @return Returns the created application protocol.
     */
    public static ApplicationProtocol createDafnyApplicationProtocol() {
        return new ApplicationProtocol(
            // Define the `dafny` ApplicationProtocol.
            // This protocol's request and response shapes are defined in DafnyProtocolFileWriter.
            Constants.DAFNY_APPLICATION_PROTOCOL_NAME,
            SymbolReference.builder()
                .symbol(createDafnyApplicationProtocolSymbol(Constants.DAFNY_PROTOCOL_REQUEST))
                .build(),
            SymbolReference.builder()
                .symbol(createDafnyApplicationProtocolSymbol(Constants.DAFNY_PROTOCOL_RESPONSE))
                .build()
        );
    }

    /**
     * Create a Symbol representing shapes inside the generated .dafny_protocol file.
     * @param symbolName
     * @return
     */
    private static Symbol createDafnyApplicationProtocolSymbol(String symbolName) {
        return Symbol.builder()
            .namespace(Constants.DAFNY_PROTOCOL_PYTHON_FILENAME, ".")
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
