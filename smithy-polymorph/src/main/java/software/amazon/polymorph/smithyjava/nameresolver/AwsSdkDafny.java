package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.TypeName;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithydafny.DafnyNameResolver.traitNameForServiceClient;


public class AwsSdkDafny extends Dafny {

    public AwsSdkDafny(ServiceShape serviceShape, Model model) {
        super(packageNameForServiceShape(serviceShape), serviceShape, model);
    }

    @Override
    TypeName typeForService(ServiceShape shape) {
        return ClassName.get(
                modelPackage,
                traitNameForServiceClient(shape));
    }

    @Override
    TypeName typeForResource(ResourceShape shape) {
        return ClassName.get(
                modelPackage,
                "I%s".formatted(StringUtils.capitalize(shape.getId().getName()))
        );
    }
}
