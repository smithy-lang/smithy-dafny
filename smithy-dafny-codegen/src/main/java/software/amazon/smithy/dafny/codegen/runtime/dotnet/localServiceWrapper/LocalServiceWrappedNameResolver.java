package software.amazon.smithy.dafny.codegen.runtime.dotnet.localServiceWrapper;

import software.amazon.smithy.dafny.codegen.runtime.dotnet.DotNetNameResolver;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

public class LocalServiceWrappedNameResolver extends DotNetNameResolver {
    public LocalServiceWrappedNameResolver(final Model model, final ServiceShape serviceShape) {
        super(model, serviceShape);
    }

    public String shimClassForService() {
        return "%sShim".formatted(getServiceName());
    }

    private String getServiceName() {
        return StringUtils.capitalize(getServiceShape().getId().getName());
    }

    public String implForServiceClient() {
        return "%s.%s"
                .formatted(
                    super.namespaceForService(),
                    clientForService()
                );
    }

    @Override
    public String namespaceForService() {
        return super.namespaceForService()  + ".Wrapped";
    }

    @Override
    public String nativeWrapperClassForResource(final ShapeId resourceShapeId) {
        return "Wrapped%s".formatted(super.nativeWrapperClassForResource(resourceShapeId));
    }

    public String qualifiedClassForBaseServiceException() {
        // TODO: Is a raw exception really the right thing to be returning?
        final String cSharpType = "System.Exception";
        return cSharpType;
    }
}
