package software.amazon.polymorph.smithypython.localservice.extensions;

import java.util.LinkedHashSet;
import java.util.Set;

import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.knowledge.ServiceIndex;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.python.codegen.*;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;
import software.amazon.smithy.python.codegen.sections.*;

import static java.lang.String.format;

public class SynchronousClientGenerator extends ClientGenerator {

    SynchronousClientGenerator(GenerationContext context, ServiceShape service) {
        super(context, service);
        //TODO Auto-generated constructor stub
    }

    @Override
    protected void generateService(PythonWriter writer) {
        var serviceSymbol = context.symbolProvider().toSymbol(service);
        var pluginSymbol = Symbol.builder()
                .name("Plugin")
                .namespace(format("%s.config", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(context.settings().getService().getNamespace(), context)), ".")
                .definitionFile(format("./%s/config.py",  SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(context.settings().getService().getNamespace())))
                .build();
        
        var configShapeId = service.getTrait(LocalServiceTrait.class).get().getConfigId();
        // TODO-Python: Create a new SymbolVisitor... Smithy-Python is dumb about 
        // knowing where classes are actually generated, and tries to import
        // the config from .models
        // var configSymbol = context.symbolProvider().toSymbol(
        //     context.model().expectShape(configShapeId)
        // );
        writer.addImport(".config", configShapeId.getName());
        
        writer.addStdlibImport("typing", "TypeVar");
        writer.write("""
            Input = TypeVar("Input")
            Output = TypeVar("Output")
            """);

        writer.openBlock("class $L:", "", serviceSymbol.getName(), () -> {
            var docs = service.getTrait(DocumentationTrait.class)
                    .map(StringTrait::getValue)
                    .orElse("Client for " + serviceSymbol.getName());
            writer.writeDocs(() -> {
                writer.write("""
                        $L

                        :param config: Configuration for the client.""", docs);
            });

            var defaultPlugins = new LinkedHashSet<SymbolReference>();

            for (PythonIntegration integration : context.integrations()) {
                for (RuntimeClientPlugin runtimeClientPlugin : integration.getClientPlugins()) {
                    if (runtimeClientPlugin.matchesService(context.model(), service)) {
                        runtimeClientPlugin.getPythonPlugin().ifPresent(defaultPlugins::add);
                    }
                }
            }
//
//            writer.write("""
//                    def __init__(
//                        self,
//                        config: $1L | None = None
//                    ):
//                        self._config = config or $1L()
//
//                        client_plugins: list[$2T] = [
//                            $3C
//                        ]
//
//                        for plugin in client_plugins:
//                            plugin(self._config)
//                    """, configShapeId.getName(), pluginSymbol, writer.consumer(w -> writeDefaultPlugins(w, defaultPlugins)));

            writer.addStdlibImport(
                DafnyNameResolver.getDafnyTypesModuleNameForSmithyNamespace(service.getId().getNamespace()),
                DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service)
            );

            writer.write("""
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

                    """, configShapeId.getName(),
                    pluginSymbol,
                    writer.consumer(w -> writeDefaultPlugins(w, defaultPlugins)),
                    DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service));

            var topDownIndex = TopDownIndex.of(context.model());
            for (ShapeId operationShapeId : service.getOperations()) {
//            for (OperationShape operation : topDownIndex.getContainedOperations(service)) {
                generateOperation(writer, context.model().expectShape(operationShapeId).asOperationShape().get());
            }
        });

        if (context.protocolGenerator() != null) {
            generateOperationExecutor(writer);
        }
    }

    @Override
    protected void generateOperation(PythonWriter writer, OperationShape operation) {
        var operationSymbol = context.symbolProvider().toSymbol(operation);

        var input = context.model().expectShape(operation.getInputShape());
//        var inputSymbol = context.symbolProvider().toSymbol(input);

        var operationInputShape = context.model().expectShape(operation.getInputShape()).asStructureShape().get();
        Symbol interceptorInputSymbol;
        if (operationInputShape.hasTrait(PositionalTrait.class)) {
            final MemberShape onlyMember = PositionalTrait.onlyMember(operationInputShape);
            final Shape targetShape = context.model().expectShape(onlyMember.getTarget());
            interceptorInputSymbol = context.symbolProvider().toSymbol(targetShape);
        } else {
            interceptorInputSymbol = context.symbolProvider().toSymbol(operationInputShape);
        }

        var operationOutputShape = context.model().expectShape(operation.getOutputShape()).asStructureShape().get();
        Symbol interceptorOutputSymbol;
        if (operationOutputShape.hasTrait(PositionalTrait.class)) {
            final MemberShape onlyMember = PositionalTrait.onlyMember(operationOutputShape);
            final Shape targetShape = context.model().expectShape(onlyMember.getTarget());
            interceptorOutputSymbol = context.symbolProvider().toSymbol(targetShape);
        } else {
            interceptorOutputSymbol = context.symbolProvider().toSymbol(operationOutputShape);
        }

        var output = context.model().expectShape(operation.getOutputShape());
//        var outputSymbol = context.symbolProvider().toSymbol(output);

        writer.openBlock("def $L(self, input: $T) -> $T:", "",
                operationSymbol.getName(), interceptorInputSymbol, interceptorOutputSymbol, () -> {
            writer.writeDocs(() -> {
                // TODO: Point to Polymorph Javadoc trait
                var docs = operation.getTrait(DocumentationTrait.class)
                        .map(StringTrait::getValue)
                        .orElse(String.format("Invokes the %s operation.", operation.getId().getName()));

                var inputDocs = input.getTrait(DocumentationTrait.class)
                        .map(StringTrait::getValue)
                        .orElse("The operation's input.");

                writer.write("""
                        $L

                        :param input: $L""", docs, inputDocs);
            });

            if (context.protocolGenerator() == null) {
                writer.write("raise NotImplementedError()");
            } else {
                var protocolGenerator = context.protocolGenerator();
                var serSymbol = protocolGenerator.getSerializationFunction(context, operation);
                var deserSymbol = protocolGenerator.getDeserializationFunction(context, operation);
                writer.addStdlibImport("asyncio");
                writer.write("""
                    return asyncio.run(self._execute_operation(
                        input=input,
                        plugins=[],
                        serialize=$T,
                        deserialize=$T,
                        config=self._config,
                        operation_name=$S,
                    ))
                    """, serSymbol, deserSymbol, operation.getId().getName());
            }
        });
    }

    protected void generateOperationExecutor(PythonWriter writer) {
        var transportRequest = context.applicationProtocol().requestType();
        var transportResponse = context.applicationProtocol().responseType();
        var errorSymbol = Symbol.builder()
                .name("ServiceError")
                .namespace(format("%s.errors", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(context.settings().getService().getNamespace(), context)), ".")
                .definitionFile(format("./%s/errors.py", SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(context.settings().getService().getNamespace())))
                .build();
        var pluginSymbol = Symbol.builder()
                .name("Plugin")
                .namespace(format("%s.config", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(context.settings().getService().getNamespace(), context)), ".")
                .definitionFile(format("./%s/config.py",  SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(context.settings().getService().getNamespace())))
                .build();

        var configSymbol = CodegenUtils.getConfigSymbol(context.settings());
        // TODO-Python make import work automatically
        writer.addImport(".config", configSymbol.getName());

        writer.addStdlibImport("typing", "Callable");
        writer.addStdlibImport("typing", "Awaitable");
        writer.addStdlibImport("typing", "cast");
        writer.addStdlibImport("copy", "deepcopy");
        writer.addStdlibImport("asyncio", "sleep");

        writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
        writer.addImport("smithy_python.exceptions", "SmithyRetryException");
        writer.addImport("smithy_python.interfaces.interceptor", "Interceptor");
        writer.addImport("smithy_python.interfaces.interceptor", "InterceptorContext");
        writer.addImport("smithy_python.interfaces.retries", "RetryErrorInfo");
        writer.addImport("smithy_python.interfaces.retries", "RetryErrorType");

        writer.indent();
        writer.write("""
                async def _execute_operation(
                    self,
                    input: Input,
                    plugins: list[$1T],
                    serialize: Callable[[Input, $5L], Awaitable[$2T]],
                    deserialize: Callable[[$3T, $5L], Awaitable[Output]],
                    config: $5L,
                    operation_name: str,
                ) -> Output:
                    try:
                        return await self._handle_execution(
                            input, plugins, serialize, deserialize, config, operation_name
                        )
                    except Exception as e:
                        # Make sure every exception that we throw is an instance of $4T so
                        # customers can reliably catch everything we throw.
                        if not isinstance(e, $4T):
                            raise $4T(e) from e
                        raise e

                async def _handle_execution(
                    self,
                    input: Input,
                    plugins: list[$1T],
                    serialize: Callable[[Input, $5L], Awaitable[$2T]],
                    deserialize: Callable[[$3T, $5L], Awaitable[Output]],
                    config: $5L,
                    operation_name: str,
                ) -> Output:
                    context: InterceptorContext[Input, None, None, None] = InterceptorContext(
                        request=input,
                        response=None,
                        transport_request=None,
                        transport_response=None,
                    )
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
                        config = deepcopy(config)
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
                        context_with_transport_request._transport_request = await serialize(
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
                            context_with_response = await self._handle_attempt(
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
                                await sleep(retry_token.retry_delay)
                            else:
                                # Step 8: Invoke record_success
                                retry_strategy.record_success(token=retry_token)
                                break
                    except Exception as e:
                        if context.response is not None:
                            # config.logger.exception(f"Exception occurred while handling: {context.response}")
                            pass
                        context._response = e

                    # At this point, the context's request will have been definitively set, and
                    # The response will be set either with the modeled output or an exception. The
                    # transport_request and transport_response may be set or None.
                    execution_context = cast(
                        InterceptorContext[Input, Output, $2T | None, $3T | None], context
                    )
                    return await self._finalize_execution(interceptors, execution_context)

                async def _handle_attempt(
                    self,
                    deserialize: Callable[[$3T, $5L], Awaitable[Output]],
                    interceptors: list[Interceptor[Input, Output, $2T, $3T]],
                    context: InterceptorContext[Input, None, $2T, None],
                    config: $5L,
                    operation_name: str,
                ) -> InterceptorContext[Input, Output, $2T, $3T | None]:
                    try:
                        # assert config.interceptors is not None
                        # Step 7a: Invoke read_before_attempt
                        for interceptor in interceptors:
                            interceptor.read_before_attempt(context)

                """, pluginSymbol, transportRequest, transportResponse, errorSymbol, configSymbol.getName());

        boolean supportsAuth = !ServiceIndex.of(context.model()).getAuthSchemes(service).isEmpty();
        writer.pushState(new ResolveIdentitySection());
        if (context.applicationProtocol().isHttpProtocol() && supportsAuth) {
            writer.pushState(new InitializeHttpAuthParametersSection());
            writer.write("""
                        # Step 7b: Invoke service_auth_scheme_resolver.resolve_auth_scheme
                        auth_parameters: $1T = $1T(
                            operation=operation_name,
                            ${2C|}
                        )

                """, CodegenUtils.getHttpAuthParamsSymbol(context.settings()),
                    writer.consumer(this::initializeHttpAuthParameters));
            writer.popState();

            writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
            writer.addImport("smithy_python.interfaces.identity", "Identity");
            writer.addImports("smithy_python.interfaces.auth", Set.of("HTTPSigner", "HTTPAuthOption"));
            writer.addStdlibImport("typing", "Any");
            writer.write("""
                        auth_options = config.http_auth_scheme_resolver.resolve_auth_scheme(
                            auth_parameters=auth_parameters
                        )
                        auth_option: HTTPAuthOption | None = None
                        for option in auth_options:
                            if option.scheme_id in config.http_auth_schemes:
                                auth_option = option

                        signer: HTTPSigner[Any, Any] | None = None
                        identity: Identity | None = None

                        if auth_option:
                            auth_scheme = config.http_auth_schemes[auth_option.scheme_id]

                            # Step 7c: Invoke auth_scheme.identity_resolver
                            identity_resolver = auth_scheme.identity_resolver(config=config)

                            # Step 7d: Invoke auth_scheme.signer
                            signer = auth_scheme.signer

                            # Step 7e: Invoke identity_resolver.get_identity
                            identity = await identity_resolver.get_identity(
                                identity_properties=auth_option.identity_properties
                            )

                """);
        }
        writer.popState();

        writer.pushState(new ResolveEndpointSection());
        if (context.applicationProtocol().isHttpProtocol()) {
            writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
            // TODO: implement the endpoints 2.0 spec and remove the hard-coded handling of static params.
            writer.addImport("smithy_python._private.http", "StaticEndpointParams");
            writer.addImport("smithy_python._private", "URI");
            writer.write("""
                        # Step 7f: Invoke endpoint_resolver.resolve_endpoint
                        if config.endpoint_resolver is None:
                            raise $1T(
                                "No endpoint_resolver found on the operation config."
                            )
                        if config.endpoint_uri is None:
                            raise $1T(
                                "No endpoint_uri found on the operation config."
                            )

                        endpoint = await config.endpoint_resolver.resolve_endpoint(
                            StaticEndpointParams(uri=config.endpoint_uri)
                        )
                        if not endpoint.uri.path:
                            path = ""
                        elif endpoint.uri.path.endswith("/"):
                            path = endpoint.uri.path[:-1]
                        else:
                            path = endpoint.uri.path
                        if context.transport_request.destination.path:
                            path += context.transport_request.destination.path
                        context._transport_request.destination = URI(
                            scheme=endpoint.uri.scheme,
                            host=context.transport_request.destination.host + endpoint.uri.host,
                            path=path,
                            query=context.transport_request.destination.query,
                        )
                        context._transport_request.fields.extend(endpoint.headers)

                """, errorSymbol);
        }
        writer.popState();

        writer.write("""
                        # Step 7g: Invoke modify_before_signing
                        for interceptor in interceptors:
                            context._transport_request = interceptor.modify_before_signing(context)

                        # Step 7h: Invoke read_before_signing
                        for interceptor in interceptors:
                            interceptor.read_before_signing(context)

                """);

        writer.pushState(new SignRequestSection());
        if (context.applicationProtocol().isHttpProtocol() && supportsAuth) {
            writer.write("""
                        # Step 7i: sign the request
                        if auth_option and signer:
                            context._transport_request = await signer.sign(
                                http_request=context.transport_request,
                                identity=identity,
                                signing_properties=auth_option.signer_properties,
                            )
                """);
        }
        writer.popState();

        writer.write("""
                        # Step 7j: Invoke read_after_signing
                        for interceptor in interceptors:
                            interceptor.read_after_signing(context)

                        # Step 7k: Invoke modify_before_transmit
                        for interceptor in interceptors:
                            context._transport_request = interceptor.modify_before_transmit(context)

                        # Step 7l: Invoke read_before_transmit
                        for interceptor in interceptors:
                            interceptor.read_before_transmit(context)

                """);

        writer.pushState(new SendRequestSection());
        if (context.applicationProtocol().isHttpProtocol()) {
            writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
            writer.addImport("smithy_python.interfaces.http", "HTTPRequestConfiguration");
            writer.write("""
                        # Step 7m: Invoke http_client.send
                        request_config = config.http_request_config or HTTPRequestConfiguration()
                        context_with_response = cast(
                            InterceptorContext[Input, None, $1T, $2T], context
                        )
                        context_with_response._transport_response = await config.http_client.send(
                            request=context_with_response.transport_request,
                            request_config=request_config,
                        )

                """, transportRequest, transportResponse);
        }
        writer.popState();

        writer.write("""
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
                        context_with_output._response = await deserialize(
                            context_with_output._transport_response, config
                        )

                        # Step 7r: Invoke read_after_deserialization
                        for interceptor in interceptors:
                            interceptor.read_after_deserialization(context_with_output)
                    except Exception as e:
                        if context.response is not None:
                            # config.logger.exception(f"Exception occurred while handling: {context.response}")
                            pass
                        context._response = e

                    # At this point, the context's request and transport_request have definitively been set,
                    # the response is either set or an exception, and the transport_resposne is either set or
                    # None. This will also be true after _finalize_attempt because there is no opportunity
                    # there to set the transport_response.
                    attempt_context = cast(
                        InterceptorContext[Input, Output, $1T, $2T | None], context
                    )
                    return await self._finalize_attempt(interceptors, attempt_context)

                async def _finalize_attempt(
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
                        if context.response is not None:
                            # config.logger.exception(f"Exception occurred while handling: {context.response}")
                            pass
                        context._response = e

                    # Step 7t: Invoke read_after_attempt
                    for interceptor in interceptors:
                        try:
                            interceptor.read_after_attempt(context)
                        except Exception as e:
                            if context.response is not None:
                                # config.logger.exception(f"Exception occurred while handling: {context.response}")
                                pass
                            context._response = e

                    return context

                async def _finalize_execution(
                    self,
                    interceptors: list[Interceptor[Input, Output, $1T, $2T]],
                    context: InterceptorContext[Input, Output, $1T | None, $2T | None],
                ) -> Output:
                    try:
                        # Step 9: Invoke modify_before_completion
                        for interceptor in interceptors:
                            context._response = interceptor.modify_before_completion(context)

                        # Step 10: Invoke trace_probe.dispatch_events
                        try:
                            pass
                        except Exception as e:
                            # log and ignore exceptions
                            # config.logger.exception(f"Exception occurred while dispatching trace events: {e}")
                            pass
                    except Exception as e:
                        if context.response is not None:
                            # config.logger.exception(f"Exception occurred while handling: {context.response}")
                            pass
                        context._response = e

                    # Step 11: Invoke read_after_execution
                    for interceptor in interceptors:
                        try:
                            interceptor.read_after_execution(context)
                        except Exception as e:
                            if context.response is not None:
                                # config.logger.exception(f"Exception occurred while handling: {context.response}")
                                pass
                            context._response = e

                    # Step 12: Return / throw
                    if isinstance(context.response, Exception):
                        raise context.response

                    # We may want to add some aspects of this context to the output types so we can
                    # return it to the end-users.
                    return context.response
                """, transportRequest, transportResponse);
        writer.dedent();
    }

}
