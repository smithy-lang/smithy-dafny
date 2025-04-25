package software.amazon.smithy.dafny.codegen;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsString;
import static software.amazon.smithy.dafny.codegen.TestUtils.make;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * These tests assert the correct failure behavior on invalid test models.
 * In the future we may want to make these dedicated unit tests just on the smithy models instead.
 */
class CodegenCliTest {

  @Test
  public void testUnsupportedShape() {
    Path testModelPath = getTestModelPath("SimpleTypes/SimpleDocument");
    RuntimeException e = Assertions.assertThrows(
      RuntimeException.class,
      () -> make(testModelPath, "polymorph_dafny")
    );
    String expectedMessage =
      "[ERROR] smithy.api#Document: smithy-dafny does not support this shape type: document. | UnsupportedFeatures";
    assertThat(e.getMessage(), containsString(expectedMessage));
  }

  @Test
  public void testUnsupportedTrait() {
    Path testModelPath = getTestModelPath("Streaming");
    RuntimeException e = Assertions.assertThrows(
      RuntimeException.class,
      () -> make(testModelPath, "polymorph_dafny")
    );
    String expectedMessage =
      "[DANGER] simple.streaming#StreamingBlob: smithy-dafny does not support this trait: smithy.api#streaming. | UnsupportedFeatures";
    assertThat(e.getMessage(), containsString(expectedMessage));
  }

  private Path getTestModelPath(String relativeTestModelPath) {
    return Paths
      .get(".")
      .resolve("..")
      .resolve("..")
      .resolve("TestModels")
      .resolve(relativeTestModelPath);
  }
}
