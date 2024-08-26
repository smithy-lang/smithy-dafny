// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk;

import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.SmithyUnstableApi;

// This will implement any handling of components outside the request body and error handling.
@SmithyUnstableApi
public abstract class DafnyPythonAwsSdkProtocolGenerator
  implements ProtocolGenerator {

  public static ApplicationProtocol DAFNY_PYTHON_AWS_SDK_PROTOCOL =
    new ApplicationProtocol(
      // Define the `dafny-python-aws-sdk-protocol` ApplicationProtocol.
      // ApplicationProtocol is distinct from the Protocols used in ProtocolGenerators.
      // We define an ApplicationProtocol that will be used by all AWS SDK shims for
      // Smithy-plugin-integrated code generators.
      // The ApplicationProtocol is used within our code to determine which code should be
      // generated.
      // The `null`s reflect that this ApplicationProtocol does not have request
      //   or response object types, since it does not use Smithy-generated clients,
      //   but is instead a wrapper for boto3.
      "dafny-python-aws-sdk-application-protocol",
      null,
      null
    );

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DAFNY_PYTHON_AWS_SDK_PROTOCOL;
  }

  @Override
  public void generateRequestSerializers(GenerationContext context) {}

  @Override
  public void generateResponseDeserializers(GenerationContext context) {}
}
