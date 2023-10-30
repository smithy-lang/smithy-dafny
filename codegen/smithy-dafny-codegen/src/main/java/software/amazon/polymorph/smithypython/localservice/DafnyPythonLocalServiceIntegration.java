// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.localservice.customize.ConfigFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.DafnyImplInterfaceFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.DafnyProtocolFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.ErrorsFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.ModelsFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.PluginFileWriter;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.ConfigProperty;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.utils.CodeSection;

public final class DafnyPythonLocalServiceIntegration implements PythonIntegration {

    private final RuntimeClientPlugin dafnyImplRuntimeClientPlugin = RuntimeClientPlugin.builder()
        .configProperties(
            // Adds a new field in the client class' config.
            // `dafnyImplInterface` is a static interface for accessing Dafny implementation code.
            // The Smithy-Dafny Python plugin generates a dafnyImplInterface file
            //   and populates it with the relevant information from the model
            //   to interact with the Dafny implementation.
            // We use a static interface as we cannot plug the model into this RuntimeClientPlugin
            //   definition, so this class cannot be aware of model shapes.
            // To work around this, we can point the RuntimeClientPlugin to a static interface
            //   that IS aware of model shapes, and plug the model in there.
            Collections.singletonList(ConfigProperty.builder()
                .name("dafnyImplInterface")
                .type(
                    Symbol.builder()
                        .name("DafnyImplInterface")
                        .namespace(".dafnyImplInterface", ".")
                        .build()
                )
                // nullable is marked as true here.
                // This allows the Config to be instantiated without providing a plugin, which
                //   is required because of how Smithy-Python generates the code.
                // However, this plugin MUST be present before using the client.
                // Immediately after the Config is instantiated, the Dafny plugin
                //   will add our plugin to the Config.
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

    /**
     * Generate all Smithy-Dafny custom Python code.
     *
     * @param codegenContext Code generation context that can be queried when writing additional
     *                       files.
     */
    @Override
    public void customize(GenerationContext codegenContext) {
        if (!codegenContext.applicationProtocol().equals(
                DafnyPythonLocalServiceProtocolGenerator.DAFNY_PYTHON_LOCAL_SERVICE_APPLICATION_PROTOCOL)) {
            return;
        }

        // Generate for service shapes with localService trait
        Set<ServiceShape> serviceShapes = Set.of(
            codegenContext.model().expectShape(codegenContext.settings().getService())
                .asServiceShape().get());

        ServiceShape serviceShape = codegenContext.model()
            .expectShape(codegenContext.settings().getService()).asServiceShape().get();

        customizeForServiceShape(serviceShape, codegenContext);

        // Get set(non-service operation shapes) = set(model operation shapes) - set(service operation shapes)
        // This is related to forking Smithy-Python. TODO: resolve when resolving fork.
        // Smithy-Python will only generate code for shapes which are used by the protocol.
        // Polymorph has a requirement to generate code for all shapes in the model,
        //   even if the service does not use those shapes.
        // (The use case is that other models may depend on shapes that are defined in this model,
        //   though not used in this model.)
        Set<ShapeId> serviceOperationShapes = serviceShapes.stream()
            .map(EntityShape::getOperations)
            .flatMap(Collection::stream)
            .collect(Collectors.toSet());
        Set<ShapeId> nonServiceOperationShapes = codegenContext.model().getOperationShapes()
            .stream()
            .map(Shape::getId)
            .filter(operationShapeId -> operationShapeId.getNamespace()
                .equals(serviceShape.getId().getNamespace()))
            .collect(Collectors.toSet());
        nonServiceOperationShapes.removeAll(serviceOperationShapes);

        customizeForNonServiceOperationShapes(nonServiceOperationShapes, codegenContext);
    }

    /**
     * Generate any code for operation shapes that are NOT part of the localService.
     *
     * @param operationShapeIds
     * @param codegenContext
     */
    private void customizeForNonServiceOperationShapes(Set<ShapeId> operationShapeIds,
            GenerationContext codegenContext) {
        new ReferencesFileWriter().customizeFileForNonServiceShapes(operationShapeIds,
                codegenContext);
    }

    /**
     * Generate any code for the localService ServiceShape.
     *
     * @param serviceShape
     * @param codegenContext
     */
    private void customizeForServiceShape(ServiceShape serviceShape, GenerationContext codegenContext) {
        new PluginFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new DafnyImplInterfaceFileWriter().customizeFileForServiceShape(serviceShape,
            codegenContext);
        new DafnyProtocolFileWriter().customizeFileForServiceShape(serviceShape,
            codegenContext);
        new ErrorsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ModelsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ConfigFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
        new ReferencesFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
    }

    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {
        return Collections.singletonList(new DafnyPythonLocalServiceProtocolGenerator() {
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
