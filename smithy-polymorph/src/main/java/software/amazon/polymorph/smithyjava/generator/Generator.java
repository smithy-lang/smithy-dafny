package software.amazon.polymorph.smithyjava.generator;

import com.google.common.base.Joiner;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.shapes.ShapeType;

public abstract class Generator {
    private static final Logger LOGGER = LoggerFactory.getLogger(Generator.class);

    public CodegenSubject subject;

    public Generator(
        CodegenSubject subject
    ) {
        this.subject = subject;
    }

    public Map<Path, TokenTree> generate() {
        final JavaFile javaFile = javaFile();
        List<String> pathPieces = Arrays
                .stream(javaFile.packageName.split("\\."))
                .collect(Collectors.toList());
        pathPieces.add(javaFile.typeSpec.name + ".java");
        final Path path = Path.of(Joiner.on('/').join(pathPieces));
        final TokenTree tokenTree = TokenTree.of(javaFile.toString());
        return Map.of(path, tokenTree);
    }

    public abstract JavaFile javaFile();

     public static class Constants {
        public static final MethodReference IDENTITY_FUNCTION = new MethodReference(
                ClassName.get(java.util.function.Function.class),
                "identity");
        public static final Set<ShapeType> SUPPORTED_CONVERSION_AGGREGATE_SHAPES;
        static {
            SUPPORTED_CONVERSION_AGGREGATE_SHAPES = Set.of(
                    ShapeType.LIST, ShapeType.SET, ShapeType.MAP
            );
        }

    }
}
