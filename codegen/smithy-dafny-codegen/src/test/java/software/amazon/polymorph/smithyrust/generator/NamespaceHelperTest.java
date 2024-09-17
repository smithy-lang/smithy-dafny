package software.amazon.polymorph.smithyrust.generator;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.Test;

public class NamespaceHelperTest {

  @Test
  public void testRustModuleForSmithyNamespace() {
    assertEquals(
      "string",
      NamespaceHelper.rustModuleForSmithyNamespace("simple.string")
    );
    assertEquals(
      "foobar",
      NamespaceHelper.rustModuleForSmithyNamespace("aws.cryptography.foobar")
    );
  }
}
