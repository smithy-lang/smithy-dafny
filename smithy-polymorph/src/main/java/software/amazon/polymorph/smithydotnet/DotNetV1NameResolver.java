package software.amazon.polymorph.smithydotnet;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

public class DotNetV1NameResolver extends DotNetNameResolver {
    public DotNetV1NameResolver(Model model, ServiceShape serviceShape) {
        super(model, serviceShape);
    }

    @Override
    public String interfaceForService(ShapeId serviceShapeId) {
        if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(serviceShapeId)) {
            return "I" + serviceShapeId.getName();
        }

        return super.interfaceForService(serviceShapeId);
    }
}
