// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator;

import com.google.common.base.Joiner;
import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ShapeType;

public abstract class Generator {

  public static final Modifier[] PUBLIC_STATIC = new Modifier[] {
    Modifier.PUBLIC,
    Modifier.STATIC,
  };
  protected static final Modifier[] PRIVATE_FINAL = new Modifier[] {
    Modifier.PRIVATE,
    Modifier.FINAL,
  };
  public static final String INTERFACE_VAR = "impl";
  public static final String INTERFACE_FIELD = "_impl";
  public static final String NATIVE_VAR = "input";
  protected static final String DAFNY_VAR = "dafnyValue";
  protected static final String RESULT_VAR = "result";

  @SuppressWarnings("unused")
  private static final Logger LOGGER = LoggerFactory.getLogger(Generator.class);

  public CodegenSubject subject;

  public Generator(CodegenSubject subject) {
    this.subject = subject;
  }

  public Map<Path, TokenTree> generate() {
    final LinkedHashMap<Path, TokenTree> rtn = new LinkedHashMap<>();
    final Set<JavaFile> javaFiles = javaFiles();
    for (JavaFile javaFile : javaFiles) {
      List<String> pathPieces = Arrays
        .stream(javaFile.packageName.split("\\."))
        .collect(Collectors.toList());
      pathPieces.add(javaFile.typeSpec.name + ".java");
      final Path path = Path.of(Joiner.on('/').join(pathPieces));
      final TokenTree tokenTree = TokenTree.of(
        // Indent
        // javaFile.toBuilder().indent("    ").build().toString()
        // Don't Indent to reduce git diff:
        javaFile.toString()
      );
      rtn.put(path, tokenTree);
    }
    return rtn;
  }

  public abstract Set<JavaFile> javaFiles();

  protected List<OperationShape> getOperationsForTarget() {
    return subject.serviceShape
      .getOperations()
      .stream()
      .sorted()
      .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
      .collect(Collectors.toList());
  }

  public static class Constants {

    public static final MethodReference IDENTITY_FUNCTION = new MethodReference(
      ClassName.get(java.util.function.Function.class),
      "identity"
    );
    public static final Set<ShapeType> LIST_MAP_SET_SHAPE_TYPES;

    static {
      LIST_MAP_SET_SHAPE_TYPES =
        Set.of(ShapeType.LIST, ShapeType.SET, ShapeType.MAP);
    }

    public static final ClassName JAVA_UTIL_STREAM_COLLECTORS = ClassName.get(
      "java.util.stream",
      "Collectors"
    );
    public static final ClassName JAVA_UTIL_ARRAYLIST = ClassName.get(
      "java.util",
      "ArrayList"
    );
    public static final ClassName JAVA_UTIL_HASHMAP = ClassName.get(
      "java.util",
      "HashMap"
    );
    public static final ClassName TESTNG_TEST = ClassName.get(
      "org.testng.annotations",
      "Test"
    );
    public static final ClassName TESTNG_ASSERT = ClassName.get(
      "org.testng",
      "Assert"
    );
  }
}
