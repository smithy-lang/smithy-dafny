package software.amazon.polymorph.smithypython.customize;

import java.util.Locale;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.PythonNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

public class PluginFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    String clientName = PythonNameResolver.clientForService(serviceShape);
    String implModulePrelude = DafnyNameResolver.getDafnyImplModuleNamespaceForShape(serviceShape);

    codegenContext.writerDelegator().useFileWriter(moduleName + "/plugin.py", "", writer -> {
      writer.write(
          """
          from .config import Config, Plugin
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
