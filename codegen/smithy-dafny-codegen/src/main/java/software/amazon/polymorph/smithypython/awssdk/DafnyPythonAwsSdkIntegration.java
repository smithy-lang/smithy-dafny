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

import java.util.ArrayList;
import java.util.List;
import software.amazon.polymorph.smithypython.awssdk.customize.AwsSdkShimFileWriter;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;

public final class DafnyPythonAwsSdkIntegration implements PythonIntegration {

    /**
     * Generate all Smithy-Dafny Python AWS SDK custom code.
     *
     * @param codegenContext Code generation context that can be queried when writing additional
     *                       files.
     */
    @Override
    public void customize(GenerationContext codegenContext) {
        // ONLY run this integration's customizations IF the codegen is using its ApplicationProtocol
        if (!codegenContext.applicationProtocol().equals(
                DafnyPythonAwsSdkProtocolGenerator.DAFNY_PYTHON_AWS_SDK_PROTOCOL)) {
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
        new AwsSdkShimFileWriter().customizeFileForServiceShape(serviceShape, codegenContext);
    }


    /**
     * Creates the Dafny ApplicationProtocol object.
     * Smithy-Python requests this object as part of the ProtocolGenerator implementation.
     *
     * @return Returns the created application protocol.
     */
    // Smithy code generators require a "protocol" trait to be present on service shapes
    //   to generate code for them.
    // (This is in contrast to Polymorph Java and .NET, which do not.)
    // Our KMS model has `awsJson1_1`; DDB has `awsJson1_0`. (SQS has neither.)
    // We do not use either of these protocols; Polymorph wraps the AWS SDK for a given language.
    // To meet the requirement for Smithy code generators to define a protocol on the service
    //   under generation, attach an `aws.polymorph#awsSdk` protocol at runtime.
    @Override
    public List<ProtocolGenerator> getProtocolGenerators() {
        List<ProtocolGenerator> protocolGenerators = new ArrayList<>();
        protocolGenerators.add(new DafnyPythonAwsSdkProtocolGenerator() {
            // Setting `awsJson1_1` here allows any services that have this protocol trait
            //   to be generated using this PythonIntegration.
            // In practice, each service SHOULD only define one protocol trait,
            //   else it is infeasible to determine which protocol will be used.
            @Override
            public ShapeId getProtocol() {
                return ShapeId.fromParts("aws.polymorph", "awsSdk");
            }
        });

        return protocolGenerators;
    }
}
