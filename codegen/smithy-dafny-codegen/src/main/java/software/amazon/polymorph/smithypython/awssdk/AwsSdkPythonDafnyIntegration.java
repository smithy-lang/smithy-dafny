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

package software.amazon.polymorph.smithypython.awssdk;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.Constants.GenerationType;
import software.amazon.polymorph.smithypython.awssdk.extensions.DafnyPythonAwsSdkProtocolGenerator;
import software.amazon.polymorph.smithypython.customize.AwsSdkShimFileWriter;
import software.amazon.polymorph.smithypython.extensions.DafnyPythonSettings;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.ConfigProperty;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;

public final class AwsSdkPythonDafnyIntegration implements PythonIntegration {

//    @Override
//    public List<? extends CodeInterceptor<? extends CodeSection, PythonWriter>>
//    interceptors(GenerationContext codegenContext) {
//        return List.of(new SendRequestInterceptor());
//    }

    /**
     * Generate all Smithy-Dafny custom Python code.
     *
     * @param codegenContext Code generation context that can be queried when writing additional
     *                       files.
     */
    @Override
    public void customize(GenerationContext codegenContext) {
        if (!codegenContext.applicationProtocol().equals(
            getProtocolGenerators().get(0).getApplicationProtocol()
        )) {
            return;
        }

        // Generate for service shapes with localService trait
        Set<ServiceShape> serviceShapes = Set.of(
            codegenContext.model().expectShape(codegenContext.settings().getService())
                .asServiceShape().get());

        ServiceShape serviceShape = codegenContext.model()
            .expectShape(codegenContext.settings().getService()).asServiceShape().get();

        customizeForServiceShape(serviceShape, codegenContext);

    }


    /**
     * Generate any code for the localService.
     *
     * @param serviceShape
     * @param codegenContext
     */
    private void customizeForServiceShape(ServiceShape serviceShape,
            GenerationContext codegenContext) {
//        if (shouldGenerateLocalService(codegenContext)) {
//            new PluginFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//            new DafnyImplInterfaceFileWriter().customizeFileForServiceShape(serviceShape,
//                codegenContext);
//            new DafnyProtocolFileWriter().customizeFileForServiceShape(serviceShape,
//                codegenContext);
//            new ErrorsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//            new ModelsFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//            new ConfigFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//            new ReferencesFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//        } if (shouldGenerateTestShim(codegenContext)) {
//            new ShimFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//        } if (shouldGenerateAwsSdkShim(codegenContext)) {
            new AwsSdkShimFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
//        }
    }

    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {
        return Collections.singletonList(new DafnyPythonAwsSdkProtocolGenerator() {
            // No protocol!
            //
            @Override
            public ShapeId getProtocol() {
                return null;
            }
        });
    }
}
