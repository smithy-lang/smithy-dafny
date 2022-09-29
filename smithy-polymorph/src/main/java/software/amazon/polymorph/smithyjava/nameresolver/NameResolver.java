package software.amazon.polymorph.smithyjava.nameresolver;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public abstract class NameResolver {
    protected final String packageName;
    protected final Model model;
    protected final ServiceShape serviceShape;
    protected final String modelPackage;

    public NameResolver(
            final String packageName,
            final ServiceShape serviceShape,
            final Model model,
            final String modelPackageName
    ) {
        this.packageName = packageName;
        this.model = model;
        this.serviceShape = serviceShape;
        this.modelPackage = modelPackageName;
    }

    public boolean isInServiceNameSpace(final ShapeId shapeId) {
        return shapeId.getNamespace().contains(serviceShape.getId().getNamespace());
    }
}
