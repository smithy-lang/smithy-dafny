package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.google.common.base.Joiner;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafny;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNative;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;

public abstract class Generator {
    AwsSdkDafny dafnyNameResolver;
    AwsSdkNative nativeNameResolver;
    Model model;
    ServiceShape serviceShape;

    public Generator(
            AwsSdk awsSdk
    ) {
        this.serviceShape = awsSdk.serviceShape;
        this.dafnyNameResolver = awsSdk.dafnyNameResolver;
        this.nativeNameResolver = awsSdk.nativeNameResolver;
        this.model = awsSdk.model;
    }

    public Generator(ServiceShape serviceShape, Model model) {
        this.serviceShape = serviceShape;
        this.dafnyNameResolver = new AwsSdkDafny(serviceShape, model);
        this.nativeNameResolver = new AwsSdkNative(serviceShape, model);
        this.model = model;
    }

    public Map<Path, TokenTree> generate() {
        final JavaFile javaFile = javaFile(serviceShape.toShapeId());
        List<String> pathPieces = Arrays
                .stream(javaFile.packageName.split("\\."))
                .collect(Collectors.toList());
        pathPieces.add(javaFile.typeSpec.name + ".java");
        final Path path = Path.of(Joiner.on('/').join(pathPieces));
        final TokenTree tokenTree = TokenTree.of(javaFile.toString());
        return Map.of(path, tokenTree);
    }

    public abstract JavaFile javaFile(final ShapeId serviceShapeId);

     public static class Constants {
        public static final MethodReference IDENTITY_FUNCTION = new MethodReference(ClassName.get(java.util.function.Function.class), "identity");
        public static final Set<ShapeType> SUPPORTED_CONVERSION_AGGREGATE_SHAPES;
        static {
            SUPPORTED_CONVERSION_AGGREGATE_SHAPES = Set.of(
                    ShapeType.LIST, ShapeType.SET, ShapeType.MAP
            );
        }

    }
}
