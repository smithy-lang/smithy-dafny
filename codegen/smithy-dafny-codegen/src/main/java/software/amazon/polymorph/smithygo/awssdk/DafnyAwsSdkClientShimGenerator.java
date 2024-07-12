package software.amazon.polymorph.smithygo.awssdk;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public class DafnyAwsSdkClientShimGenerator implements Runnable {

    private final GenerationContext context;
    private final ServiceShape service;
    private final GoDelegator writerDelegator;
    private final Model model;
    private final SymbolProvider symbolProvider;

    public DafnyAwsSdkClientShimGenerator(GenerationContext context, ServiceShape service) {
        this.context = context;
        this.service = service;
        model = context.model();
        writerDelegator = context.writerDelegator();
        symbolProvider = context.symbolProvider();
    }

    @Override
    public void run() {
        generateShim();
    }

    void generateShim() {
        final var namespace = "%swrapped".formatted(DafnyNameResolver.dafnyNamespace(service));

        writerDelegator.useFileWriter("%s/shim.go".formatted(namespace), namespace, writer -> {

            writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(context.settings().getService().getNamespace()), DafnyNameResolver.dafnyTypesNamespace(service));
            writer.addImportFromModule("github.com/dafny-lang/DafnyStandardLibGo", "Wrappers");
            writer.addUseImports(SmithyGoDependency.CONTEXT);
            writer.addImportFromModule(SmithyNameResolver.getGoModuleNameForSmithyNamespace(context.settings().getService().getNamespace()), SmithyNameResolver.shapeNamespace(service));

            writer.write("""
                                 type Shim struct {
                                     $L
                                     client *$L.Client
                                 }
                                 """,
                         DafnyNameResolver.getDafnyInterfaceClient(service),
                         SmithyNameResolver.shapeNamespace(service)
            );


            service.getOperations().forEach(operation -> {
                final var operationShape = model.expectShape(operation, OperationShape.class);
                final var inputShape = model.expectShape(operationShape.getInputShape());
                final var outputShape = model.expectShape(operationShape.getOutputShape());
                final var inputType = inputShape.hasTrait(UnitTypeTrait.class) ? ""
                                                                               : "input %s".formatted(DafnyNameResolver.getDafnyType(inputShape, symbolProvider.toSymbol(inputShape)));

                final var typeConversion = inputShape.hasTrait(UnitTypeTrait.class) ? ""
                                                                                    : "var native_request = %s(input)".formatted(SmithyNameResolver.getFromDafnyMethodName(inputShape, ""));

                final var clientCall = "shim.client.%s(context.Background() %s)".formatted(operationShape.getId().getName(),
                                                                                           inputShape.hasTrait(UnitTypeTrait.class) ? "" : ", native_request");

                String clientResponse, returnResponse;
                if (outputShape.hasTrait(UnitTypeTrait.class)) {
                    clientResponse = "var native_error";
                    returnResponse = "dafny.TupleOf()";
                    writer.addImportFromModule("github.com/dafny-lang/DafnyRuntimeGo", "dafny");
                } else {
                    clientResponse = "var native_response, native_error";
                    returnResponse = "%s(*native_response)".formatted(SmithyNameResolver.getToDafnyMethodName(outputShape, ""));
                }

                writer.write("""
                                       func (shim *Shim) $L($L) Wrappers.Result {
                                           $L
                                           $L = $L
                                           if native_error != nil {
                                               return Wrappers.Companion_Result_.Create_Failure_($L.Error_ToDafny(native_error))
                                           }
                                           return Wrappers.Companion_Result_.Create_Success_($L)
                                       }
                                     """,
                             operationShape.getId().getName(),
                             inputType, typeConversion, clientResponse, clientCall,
                             SmithyNameResolver.shapeNamespace(service),
                             returnResponse
                );
            });
        });
    }
}
