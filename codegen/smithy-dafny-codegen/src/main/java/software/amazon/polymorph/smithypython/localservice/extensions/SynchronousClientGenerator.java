package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.LinkedHashSet;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.DafnyLocalServiceCodegenConstants;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.python.codegen.*;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.python.codegen.sections.*;

/**
 * Custom client generator. The generated Smithy-Python client generates all of its methods as
 * `async`. To use generated clients, library consumers would need to wrap calls as async. However,
 * generated Dafny code is NOT thread safe, and MUST NOT be used in an async environment. To guard
 * users against this, make all user-exposed methods on the client synchronous. This class exists to
 * provide a synchronous client interface; however, since it exists, we also remove some logic that
 * is not used by Smithy-Dafny Python clients (primarily HTTP-request-wrapping logic for
 * Smithy-Python clients).
 */
public class SynchronousClientGenerator extends ClientGenerator {

  SynchronousClientGenerator(GenerationContext context, ServiceShape service) {
    super(context, service);
  }

  /**
   * Override Smithy-Python's `generateService` to reference the Config shape from the correct module,
   *
   * @param writer
   */
  @Override
  protected void generateService(PythonWriter writer) {
    var serviceSymbol = context.symbolProvider().toSymbol(service);
    var pluginSymbol = Symbol
      .builder()
      .name("Plugin")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();

    var configShapeId = service
      .getTrait(LocalServiceTrait.class)
      .get()
      .getConfigId();
    writer.addImport(".config", configShapeId.getName());

    writer.addStdlibImport("typing", "TypeVar");
    writer.write(
      """
      Input = TypeVar("Input")
      Output = TypeVar("Output")
      """
    );

    writer.openBlock(
      "class $L:",
      "",
      serviceSymbol.getName(),
      () -> {
        var docs = service
          .getTrait(DocumentationTrait.class)
          .map(StringTrait::getValue)
          .orElse("Client for " + serviceSymbol.getName());
        writer.writeDocs(() -> {
          writer.write(
            """
            $L

            :param config: Configuration for the client.""",
            docs
          );
        });

        var defaultPlugins = new LinkedHashSet<SymbolReference>();

        for (PythonIntegration integration : context.integrations()) {
          for (RuntimeClientPlugin runtimeClientPlugin : integration.getClientPlugins()) {
            if (runtimeClientPlugin.matchesService(context.model(), service)) {
              runtimeClientPlugin
                .getPythonPlugin()
                .ifPresent(defaultPlugins::add);
            }
          }
        }

        writer.addStdlibImport(
          DafnyNameResolver.getDafnyTypesModuleNameForSmithyNamespace(
            service.getId().getNamespace(),
            context
          ),
          DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service)
        );

        writer.write(
          """
          def __init__(
              self,
              config: $1L | None = None,
              dafny_client: $4L | None = None
          ):
              if config is None:
                  self._config = Config()
              else:
                  self._config = config

              client_plugins: list[$2T] = [
                  $3C
              ]

              for plugin in client_plugins:
                  plugin(self._config)

              if dafny_client is not None:
                  self._config.dafnyImplInterface.impl = dafny_client

          """,
          configShapeId.getName(),
          pluginSymbol,
          writer.consumer(w -> writeDefaultPlugins(w, defaultPlugins)),
          DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service)
        );

        for (ShapeId operationShapeId : service.getOperations()) {
          generateOperation(
            writer,
            context
              .model()
              .expectShape(operationShapeId)
              .asOperationShape()
              .get()
          );
        }
      }
    );

    if (context.protocolGenerator() != null) {
      generateOperationExecutor(writer);
    }
  }

  /**
   * Override Smithy-Python to generate correct operations considering {@link PositionalTrait}s
   * and {@link ReferenceTrait}s.
   *
   * @param writer
   * @param operation
   */
  @Override
  protected void generateOperation(
    PythonWriter writer,
    OperationShape operation
  ) {
    var operationSymbol = context.symbolProvider().toSymbol(operation);

    var input = context.model().expectShape(operation.getInputShape());

    var operationInputShape = context
      .model()
      .expectShape(operation.getInputShape())
      .asStructureShape()
      .get();

    // "visible" in the sense that this the actual input/output shape considering the @positional
    // trait
    Shape visibleOperationInputShape;
    Symbol interceptorInputSymbol;

    if (operationInputShape.hasTrait(PositionalTrait.class)) {
      final MemberShape onlyMember = PositionalTrait.onlyMember(
        operationInputShape
      );
      visibleOperationInputShape =
        context.model().expectShape(onlyMember.getTarget());
    } else {
      visibleOperationInputShape = operationInputShape;
    }

    interceptorInputSymbol =
      context.symbolProvider().toSymbol(visibleOperationInputShape);

    var operationOutputShape = context
      .model()
      .expectShape(operation.getOutputShape())
      .asStructureShape()
      .get();
    // "visible" in the sense that this the actual input/output shape considering the @positional
    // trait
    Shape visibleOperationOutputShape;
    Symbol interceptorOutputSymbol;

    if (operationOutputShape.hasTrait(PositionalTrait.class)) {
      final MemberShape onlyMember = PositionalTrait.onlyMember(
        operationOutputShape
      );
      visibleOperationOutputShape =
        context.model().expectShape(onlyMember.getTarget());
    } else {
      visibleOperationOutputShape = operationOutputShape;
    }

    interceptorOutputSymbol =
      context.symbolProvider().toSymbol(visibleOperationOutputShape);

    if (visibleOperationInputShape.hasTrait(ReferenceTrait.class)) {
      writer.addStdlibImport(interceptorInputSymbol.getNamespace());
    }
    if (visibleOperationOutputShape.hasTrait(ReferenceTrait.class)) {
      writer.addStdlibImport(interceptorOutputSymbol.getNamespace());
    }

    writer.openBlock(
      "def $L(self, input: %1$s) -> %2$s:".formatted(
          visibleOperationInputShape.hasTrait(ReferenceTrait.class)
            ? "'$L'"
            : "$T",
          visibleOperationOutputShape.hasTrait(ReferenceTrait.class)
            ? "'$L'"
            : "$T"
        ),
      "",
      operationSymbol.getName(),
      visibleOperationInputShape.hasTrait(ReferenceTrait.class)
        ? interceptorInputSymbol.getNamespace() +
        "." +
        interceptorInputSymbol.getName()
        : interceptorInputSymbol,
      visibleOperationOutputShape.hasTrait(ReferenceTrait.class)
        ? interceptorOutputSymbol.getNamespace() +
        "." +
        interceptorOutputSymbol.getName()
        : interceptorOutputSymbol,
      () -> {
        writer.writeDocs(() -> {
          var docs = operation
            .getTrait(DocumentationTrait.class)
            .map(StringTrait::getValue)
            .orElse(
              String.format(
                "Invokes the %s operation.",
                operation.getId().getName()
              )
            );

          var inputDocs = input
            .getTrait(DocumentationTrait.class)
            .map(StringTrait::getValue)
            .orElse("The operation's input.");

          writer.write(
            """
            $L

            :param input: $L""",
            docs,
            inputDocs
          );
        });

        if (context.protocolGenerator() == null) {
          writer.write("raise NotImplementedError()");
        } else {
          var protocolGenerator = context.protocolGenerator();
          var serSymbol = protocolGenerator.getSerializationFunction(
            context,
            operation
          );
          var deserSymbol = protocolGenerator.getDeserializationFunction(
            context,
            operation
          );
          writer.write(
            """
            return self._execute_operation(
                input=input,
                plugins=[],
                serialize=$T,
                deserialize=$T,
                config=self._config,
                operation_name=$S,
            )
            """,
            serSymbol,
            deserSymbol,
            operation.getId().getName()
          );
        }
      }
    );
  }

  /**
   * Override Smithy-Python's generateOperationExecutor. This MUST be done because Smithy-Python
   * does not let us intercept its SymbolProvider from within this function. We also remove code
   * that will not be used by Smithy-Dafny Python clients, around HTTP request signing and
   * authentication.
   *
   * @param writer
   */
  protected void generateOperationExecutor(PythonWriter writer) {
    var transportRequest = context.applicationProtocol().requestType();
    var transportResponse = context.applicationProtocol().responseType();
    var errorSymbol = Symbol
      .builder()
      .name("ServiceError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getPythonModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();
    var pluginSymbol = Symbol
      .builder()
      .name("Plugin")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getPythonModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();

    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());
    writer.addImport(".config", configSymbol.getName());

    writer.addStdlibImport("typing", "Callable");
    writer.addStdlibImport("typing", "cast");

    writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
    writer.addImport("smithy_python.exceptions", "SmithyRetryException");
    writer.addImport("smithy_python.interfaces.interceptor", "Interceptor");
    writer.addImport(
      "smithy_python.interfaces.interceptor",
      "InterceptorContext"
    );
    writer.addImport("smithy_python.interfaces.retries", "RetryErrorInfo");
    writer.addImport("smithy_python.interfaces.retries", "RetryErrorType");

    writer.indent();
    writer.write(
      """
      def _execute_operation(
          self,
          input: Input,
          plugins: list[$1T],
          serialize: Callable[[Input, $5L], $2T],
          deserialize: Callable[[$3T, $5L], Output],
          config: $5L,
          operation_name: str,
      ) -> Output:
          try:
              return self._handle_execution(
                  input, plugins, serialize, deserialize, config, operation_name
              )
          except Exception as e:
              # Make sure every exception that we throw is an instance of $4T so
              # customers can reliably catch everything we throw.
              if not isinstance(e, $4T):
                  raise $4T(e) from e
              raise e

      def _handle_execution(
          self,
          input: Input,
          plugins: list[$1T],
          serialize: Callable[[Input, $5L], $2T],
          deserialize: Callable[[$3T, $5L], Output],
          config: $5L,
          operation_name: str,
      ) -> Output:
          context: InterceptorContext[Input, None, None, None] = InterceptorContext(
              request=input,
              response=None,
              transport_request=None,
              transport_response=None,
          )
          try:
            _client_interceptors = config.interceptors
          except AttributeError:
            config.interceptors = []
            _client_interceptors = config.interceptors
          client_interceptors = cast(
              list[Interceptor[Input, Output, $2T, $3T]], _client_interceptors
          )
          interceptors = client_interceptors

          try:
              # Step 1a: Invoke read_before_execution on client-level interceptors
              for interceptor in client_interceptors:
                  interceptor.read_before_execution(context)

              # Step 1b: Run operation-level plugins
              for plugin in plugins:
                  plugin(config)

              _client_interceptors = config.interceptors
              interceptors = cast(
                  list[Interceptor[Input, Output, $2T, $3T]],
                  _client_interceptors,
              )

              # Step 1c: Invoke the read_before_execution hooks on newly added
              # interceptors.
              for interceptor in interceptors:
                  if interceptor not in client_interceptors:
                      interceptor.read_before_execution(context)

              # Step 2: Invoke the modify_before_serialization hooks
              for interceptor in interceptors:
                  context._request = interceptor.modify_before_serialization(context)

              # Step 3: Invoke the read_before_serialization hooks
              for interceptor in interceptors:
                  interceptor.read_before_serialization(context)

              # Step 4: Serialize the request
              context_with_transport_request = cast(
                  InterceptorContext[Input, None, $2T, None], context
              )
              context_with_transport_request._transport_request = serialize(
                  context_with_transport_request.request, config
              )

              # Step 5: Invoke read_after_serialization
              for interceptor in interceptors:
                  interceptor.read_after_serialization(context_with_transport_request)

              # Step 6: Invoke modify_before_retry_loop
              for interceptor in interceptors:
                  context_with_transport_request._transport_request = (
                      interceptor.modify_before_retry_loop(context_with_transport_request)
                  )

              # Step 7: Acquire the retry token.
              retry_strategy = config.retry_strategy
              retry_token = retry_strategy.acquire_initial_retry_token()

              while True:
                  # Make an attempt, creating a copy of the context so we don't pass
                  # around old data.
                  context_with_response = self._handle_attempt(
                      deserialize,
                      interceptors,
                      context_with_transport_request.copy(),
                      config,
                      operation_name,
                  )

                  # We perform this type-ignored re-assignment because `context` needs
                  # to point at the latest context so it can be generically handled
                  # later on. This is only an issue here because we've created a copy,
                  # so we're no longer simply pointing at the same object in memory
                  # with different names and type hints. It is possible to address this
                  # without having to fall back to the type ignore, but it would impose
                  # unnecessary runtime costs.
                  context = context_with_response  # type: ignore

                  if isinstance(context_with_response.response, Exception):
                      # Step 7u: Reacquire retry token if the attempt failed
                      try:
                          retry_token = retry_strategy.refresh_retry_token_for_retry(
                              token_to_renew=retry_token,
                              error_info=RetryErrorInfo(
                                  # TODO: Determine the error type.
                                  error_type=RetryErrorType.CLIENT_ERROR,
                              )
                          )
                      except SmithyRetryException:
                          raise context_with_response.response
                  else:
                      # Step 8: Invoke record_success
                      retry_strategy.record_success(token=retry_token)
                      break
          except Exception as e:
              context._response = e

          # At this point, the context's request will have been definitively set, and
          # The response will be set either with the modeled output or an exception. The
          # transport_request and transport_response may be set or None.
          execution_context = cast(
              InterceptorContext[Input, Output, $2T | None, $3T | None], context
          )
          return self._finalize_execution(interceptors, execution_context)

      def _handle_attempt(
          self,
          deserialize: Callable[[$3T, $5L], Output],
          interceptors: list[Interceptor[Input, Output, $2T, $3T]],
          context: InterceptorContext[Input, None, $2T, None],
          config: $5L,
          operation_name: str,
      ) -> InterceptorContext[Input, Output, $2T, $3T | None]:
          try:
              # Step 7a: Invoke read_before_attempt
              for interceptor in interceptors:
                  interceptor.read_before_attempt(context)

      """,
      pluginSymbol,
      transportRequest,
      transportResponse,
      errorSymbol,
      configSymbol.getName()
    );

    writer.pushState(new SendRequestSection());
    writer.write(
      """
              # Step 7m: Involve client Dafny impl
              if config.dafnyImplInterface.impl is None:
                  raise Exception("No impl found on the operation config.")

              context_with_response = cast(
                  InterceptorContext[Input, None, $L, $L], context
              )

              context_with_response._transport_response = config.dafnyImplInterface.handle_request(
                  input=context_with_response.transport_request
              )
      """,
      DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST,
      DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_RESPONSE
    );
    writer.popState();

    writer.write(
      """
              # Step 7n: Invoke read_after_transmit
              for interceptor in interceptors:
                  interceptor.read_after_transmit(context_with_response)

              # Step 7o: Invoke modify_before_deserialization
              for interceptor in interceptors:
                  context_with_response._transport_response = (
                      interceptor.modify_before_deserialization(context_with_response)
                  )

              # Step 7p: Invoke read_before_deserialization
              for interceptor in interceptors:
                  interceptor.read_before_deserialization(context_with_response)

              # Step 7q: deserialize
              context_with_output = cast(
                  InterceptorContext[Input, Output, $1T, $2T],
                  context_with_response,
              )
              context_with_output._response = deserialize(
                  context_with_output._transport_response, config
              )

              # Step 7r: Invoke read_after_deserialization
              for interceptor in interceptors:
                  interceptor.read_after_deserialization(context_with_output)
          except Exception as e:
              context._response = e

          # At this point, the context's request and transport_request have definitively been set,
          # the response is either set or an exception, and the transport_resposne is either set or
          # None. This will also be true after _finalize_attempt because there is no opportunity
          # there to set the transport_response.
          attempt_context = cast(
              InterceptorContext[Input, Output, $1T, $2T | None], context
          )
          return self._finalize_attempt(interceptors, attempt_context)

      def _finalize_attempt(
          self,
          interceptors: list[Interceptor[Input, Output, $1T, $2T]],
          context: InterceptorContext[Input, Output, $1T, $2T | None],
      ) -> InterceptorContext[Input, Output, $1T, $2T | None]:
          # Step 7s: Invoke modify_before_attempt_completion
          try:
              for interceptor in interceptors:
                  context._response = interceptor.modify_before_attempt_completion(
                      context
                  )
          except Exception as e:
              context._response = e

          # Step 7t: Invoke read_after_attempt
          for interceptor in interceptors:
              try:
                  interceptor.read_after_attempt(context)
              except Exception as e:
                  context._response = e

          return context

      def _finalize_execution(
          self,
          interceptors: list[Interceptor[Input, Output, $1T, $2T]],
          context: InterceptorContext[Input, Output, $1T | None, $2T | None],
      ) -> Output:
          try:
              # Step 9: Invoke modify_before_completion
              for interceptor in interceptors:
                  context._response = interceptor.modify_before_completion(context)

          except Exception as e:
              context._response = e

          # Step 11: Invoke read_after_execution
          for interceptor in interceptors:
              try:
                  interceptor.read_after_execution(context)
              except Exception as e:
                  context._response = e

          # Step 12: Return / throw
          if isinstance(context.response, Exception):
              raise context.response

          # We may want to add some aspects of this context to the output types so we can
          # return it to the end-users.
          return context.response
      """,
      transportRequest,
      transportResponse
    );
    writer.dedent();
  }
}
