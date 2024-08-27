// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.python.codegen.GenerationContext;

/**
 * Writes the plugin.py file. This file contains logic to load the Dafny plugin into the
 * Smithy-Python client.py's Config member. It also defines the Config's retry strategy ("never
 * retry" -- this is not a service).
 */
public class PluginFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    String implModulePrelude =
      DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(
        serviceShape,
        codegenContext
      );
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );
    final StructureShape configShape = codegenContext
      .model()
      .expectShape(localServiceTrait.getConfigId(), StructureShape.class);

    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/plugin.py",
        "",
        writer -> {
          writer.write(
            """
            from .config import Config, Plugin, smithy_config_to_dafny_config, $L
            from smithy_python.interfaces.retries import RetryStrategy
            from smithy_python.exceptions import SmithyRetryException
            from .dafnyImplInterface import DafnyImplInterface

            def set_config_impl(config: Config):
                ""\"
                Set the Dafny-compiled implementation in the Smithy-Python client Config
                and load our custom NoRetriesStrategy.
                ""\"
                config.dafnyImplInterface = DafnyImplInterface()
                if isinstance(config, $L):
                    from $L import default__
                    config.dafnyImplInterface.impl = default__.$L(smithy_config_to_dafny_config(config)).value
                config.retry_strategy = NoRetriesStrategy()

            class ZeroRetryDelayToken:
                ""\"
                Placeholder class required by Smithy-Python client implementation.
                Do not wait to retry.
                ""\"
                retry_delay = 0

            class NoRetriesStrategy(RetryStrategy):
                ""\"
                Placeholder class required by Smithy-Python client implementation.
                Do not retry calling Dafny code.
                ""\"
                def acquire_initial_retry_token(self):
                    return ZeroRetryDelayToken()

                def refresh_retry_token_for_retry(self, token_to_renew, error_info):
                    # Do not retry
                    raise SmithyRetryException()
                    """,
            configShape.getId().getName(),
            configShape.getId().getName(),
            implModulePrelude,
            localServiceTrait.getSdkId()
          );
        }
      );
  }
}
