// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice;

import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.SmithyUnstableApi;

@SmithyUnstableApi
public abstract class DafnyPythonWrappedLocalServiceProtocolGenerator
  implements ProtocolGenerator {

  public static ApplicationProtocol DAFNY_PYTHON_WRAPPED_LOCAL_SERVICE_PROTOCOL =
    new ApplicationProtocol(
      // Define the `dafny-python-wrapped-local-service-application-protocol`
      // ApplicationProtocol.
      // ApplicationProtocol is distinct from the Protocols used in ProtocolGenerators.
      // The ApplicationProtocol is used within our code to determine which code should be
      // generated.
      // The `null`s reflect that this ApplicationProtocol does not have request
      //   or response object types, since it does not use Smithy-generated clients.
      "dafny-python-wrapped-local-service-application-protocol",
      null,
      null
    );

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DAFNY_PYTHON_WRAPPED_LOCAL_SERVICE_PROTOCOL;
  }

  @Override
  public void generateRequestSerializers(GenerationContext context) {}

  @Override
  public void generateResponseDeserializers(GenerationContext context) {}
}
