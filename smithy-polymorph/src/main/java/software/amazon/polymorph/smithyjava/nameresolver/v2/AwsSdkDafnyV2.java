package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithydafny.DafnyNameResolver.traitNameForServiceClient;


public class AwsSdkDafnyV2 extends Dafny {

    public AwsSdkDafnyV2(ServiceShape serviceShape, Model model) {
        super(packageNameForServiceShape(serviceShape), model, serviceShape);
    }

    @Override
    ClassName classNameForService(ServiceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            return ClassName.get(
                    modelPackageNameForNamespace(shape.getId().getNamespace()),
                    traitNameForServiceClient(shape)
            );
        }
        return super.classNameForService(shape);
    }

    @Override
    ClassName classNameForResource(ResourceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            return ClassName.get(
                    modelPackageNameForNamespace(shape.getId().getNamespace()),
                    "I%s".formatted(StringUtils.capitalize(shape.getId().getName()))
            );
        }
        return super.classNameForResource(shape);
    }
}
