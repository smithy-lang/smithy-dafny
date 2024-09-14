package software.amazon.polymorph.smithyrust.generator;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.Test;

public class NamespaceHelperTest {

  @Test
  public void testRustModuleForSmithyNamespace() {
    assertEquals(
      "simple_string",
      NamespaceHelper.rustModuleForSmithyNamespace("simple.string")
    );
    assertEquals(
      "aws_cryptography_foobar",
      NamespaceHelper.rustModuleForSmithyNamespace("aws.cryptography.foobar")
    );
  }
}
