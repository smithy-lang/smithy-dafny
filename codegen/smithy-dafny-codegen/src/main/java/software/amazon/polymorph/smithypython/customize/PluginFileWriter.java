package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

/**
 * Writes the plugin.py file.
 * This file contains logic to load the Dafny plugin into the
 * Smithy-Python client.py's Config member.
 * It also defines the Config's retry strategy ("never retry" -- this is not a service).
 */
public class PluginFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    String clientName = SmithyNameResolver.clientForService(serviceShape);
    String implModulePrelude = DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(serviceShape);

    codegenContext.writerDelegator().useFileWriter(moduleName + "/plugin.py", "", writer -> {
      writer.write(
          """
          from .config import Config, Plugin, smithy_config_to_dafny_config
          from smithy_python.interfaces.retries import RetryStrategy
          from smithy_python.exceptions import SmithyRetryException
          from .dafnyImplInterface import DafnyImplInterface
          
          def set_config_impl(config: Config):
              '''
              Set the Dafny-compiled implementation in the Smithy-Python client Config
              and load our custom NoRetriesStrategy.
              '''
              from $L import $L
              config.dafnyImplInterface = DafnyImplInterface()
              config.dafnyImplInterface.impl = $L()
              config.dafnyImplInterface.impl.ctor__(smithy_config_to_dafny_config(config))
              config.retry_strategy = NoRetriesStrategy()
          
          class ZeroRetryDelayToken:
              '''
              Placeholder class required by Smithy-Python client implementation.
              Do not wait to retry.
              '''
              retry_delay = 0
          
          class NoRetriesStrategy(RetryStrategy):
              '''
              Placeholder class required by Smithy-Python client implementation.
              Do not retry calling Dafny code.
              '''
              def acquire_initial_retry_token(self):
                  return ZeroRetryDelayToken()
          
              def refresh_retry_token_for_retry(self, token_to_renew, error_info):
                  # Do not retry
                  raise SmithyRetryException()
                  """, implModulePrelude, clientName, clientName
      );
    });
  }
}
