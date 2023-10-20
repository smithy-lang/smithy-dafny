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

package software.amazon.polymorph.smithypython.wrappedlocalservice;

import java.util.Collections;
import java.util.List;
import software.amazon.polymorph.smithypython.wrappedlocalservice.customize.ShimFileWriter;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;

public final class DafnyPythonWrappedLocalServiceIntegration implements PythonIntegration {

    /**
     * Generate all custom code for wrapped LocalServices.
     *
     * @param codegenContext Code generation context that can be queried when writing additional
     *                       files.
     */
    @Override
    public void customize(GenerationContext codegenContext) {
        // ONLY run this integration's customizations if the codegen is using wrapped localService
        if (!codegenContext.applicationProtocol().equals(
                DafnyPythonWrappedLocalServiceProtocolGenerator.DAFNY_PYTHON_WRAPPED_LOCAL_SERVICE_PROTOCOL)) {
            return;
        }

        customizeForServiceShape(codegenContext.settings().getService(codegenContext.model()), codegenContext);
    }

    /**
     * Generate any code for the serviceShape.
     *
     * @param serviceShape
     * @param codegenContext
     */
    private void customizeForServiceShape(ServiceShape serviceShape,
            GenerationContext codegenContext) {
        new ShimFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
    }

    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {
        return Collections.singletonList(new DafnyPythonWrappedLocalServiceProtocolGenerator() {
            @Override
            public ShapeId getProtocol() {
                return ShapeId.from("aws.polymorph#wrappedLocalService");
            }
        });
    }
}
