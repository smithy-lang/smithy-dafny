package software.amazon.smithy.dafny.codegen.runtime.java.nameresolver;

import com.squareup.javapoet.ClassName;

import software.amazon.smithy.dafny.codegen.runtime.java.generator.CodegenSubject;
import software.amazon.smithy.dafny.codegen.utils.AwsSdkNameResolverHelpers;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.smithy.dafny.codegen.DafnyNameResolver.traitNameForServiceClient;
import static software.amazon.smithy.dafny.codegen.utils.DafnyNameResolverHelpers.dafnyCompilesExtra_;


public class AwsSdkDafnyV1 extends Dafny {

    public AwsSdkDafnyV1(ServiceShape serviceShape, Model model) {
        super(packageNameForServiceShape(serviceShape), model, serviceShape, CodegenSubject.AwsSdkVersion.V1);
    }

    @Override
    ClassName classNameForService(ServiceShape shape) {
        if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
            return classNameForAwsService(shape);
        }
        return super.classNameForService(shape);
    }

    public static ClassName classNameForAwsService(ServiceShape shape) {
        return ClassName.get(
                modelPackageNameForNamespace(shape.getId().getNamespace()),
                dafnyCompilesExtra_(traitNameForServiceClient(shape))
        );
    }

    @Override
    ClassName classNameForResource(ResourceShape shape) {
        if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
            return classNameForAwsResource(shape);
        }
        return super.classNameForResource(shape);
    }

    public static ClassName classNameForAwsResource(ResourceShape shape) {
        return ClassName.get(
                modelPackageNameForNamespace(shape.getId().getNamespace()),
                dafnyCompilesExtra_("I%s".formatted(StringUtils.capitalize(shape.getId().getName())))
        );
    }
}
