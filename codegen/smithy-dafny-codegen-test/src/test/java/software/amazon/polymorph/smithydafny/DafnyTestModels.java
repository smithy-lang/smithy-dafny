// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import static software.amazon.smithy.dafny.codegen.TestUtils.make;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

class DafnyTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleDocument");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    DISABLED_TESTS.add("Streaming");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  protected void testModels(String relativeTestModelPath) {
    super.testModels(relativeTestModelPath);

    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "polymorph_dafny");
    make(
      testModelPath,
      "verify",
      "CORES=" + Runtime.getRuntime().availableProcessors()
    );
    make(testModelPath, "dafny-reportgenerator");
  }
}
