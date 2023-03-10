package software.amazon.polymorph.smithydotnet;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class DotNetV2NameResolver extends DotNetNameResolver {
    public DotNetV2NameResolver(Model model, ServiceShape serviceShape) {
        super(model, serviceShape);
    }

    @Override
    public String interfaceForService(ShapeId serviceShapeId) {
        if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(serviceShapeId)) {
            // TODO: This may not be adequate in general
            return "I" + serviceShapeId.getName().replace("_", "__");
        }

        return super.interfaceForService(serviceShapeId);
    }
}
