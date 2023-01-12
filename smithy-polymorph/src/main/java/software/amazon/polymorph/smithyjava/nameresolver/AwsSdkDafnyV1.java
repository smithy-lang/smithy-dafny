package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithydafny.DafnyNameResolver.traitNameForServiceClient;


public class AwsSdkDafnyV1 extends Dafny {

    public AwsSdkDafnyV1(ServiceShape serviceShape, Model model) {
        super(packageNameForServiceShape(serviceShape), model, serviceShape);
    }

    @Override
    ClassName classNameForService(ServiceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            return classNameForAwsService(shape);
        }
        return super.classNameForService(shape);
    }

    public static ClassName classNameForAwsService(ServiceShape shape) {
        return ClassName.get(
                modelPackageNameForNamespace(shape.getId().getNamespace()),
                traitNameForServiceClient(shape)
        );
    }

    @Override
    ClassName classNameForResource(ResourceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            return classNameForAwsResource(shape);
        }
        return super.classNameForResource(shape);
    }

    public static ClassName classNameForAwsResource(ResourceShape shape) {
        return ClassName.get(
                modelPackageNameForNamespace(shape.getId().getNamespace()),
                "I%s".formatted(StringUtils.capitalize(shape.getId().getName()))
        );
    }
}
