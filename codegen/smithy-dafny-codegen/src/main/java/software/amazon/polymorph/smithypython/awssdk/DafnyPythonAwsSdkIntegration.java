// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

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
   *     files.
   */
  @Override
  public void customize(GenerationContext codegenContext) {
    // ONLY run this integration's customizations IF the codegen is using its ApplicationProtocol
    if (
      !codegenContext
        .applicationProtocol()
        .equals(
          DafnyPythonAwsSdkProtocolGenerator.DAFNY_PYTHON_AWS_SDK_PROTOCOL
        )
    ) {
      return;
    }

    customizeForServiceShape(
      codegenContext.settings().getService(codegenContext.model()),
      codegenContext
    );
  }

  /**
   * Generate any code for the serviceShape.
   *
   * @param serviceShape
   * @param codegenContext
   */
  private void customizeForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    new AwsSdkShimFileWriter()
      .customizeFileForServiceShape(serviceShape, codegenContext);
  }

  /**
   * Creates the Dafny ApplicationProtocol object. Smithy-Python requests this object as part of the
   * ProtocolGenerator implementation. This uses the {@link
   * software.amazon.polymorph.traits.DafnyAwsSdkProtocolTrait}.
   *
   * @return Returns the created application protocol.
   */
  @Override
  public List<ProtocolGenerator> getProtocolGenerators() {
    List<ProtocolGenerator> protocolGenerators = new ArrayList<>();
    protocolGenerators.add(
      new DafnyPythonAwsSdkProtocolGenerator() {
        // Setting a Polymorph-specific protocol allows any services that
        // have this protocol trait to be generated using this PythonIntegration.
        // See DafnyAwsSdkProtocolTrait class.
        @Override
        public ShapeId getProtocol() {
          return ShapeId.fromParts("aws.polymorph", "awsSdk");
        }
      }
    );

    return protocolGenerators;
  }
}
