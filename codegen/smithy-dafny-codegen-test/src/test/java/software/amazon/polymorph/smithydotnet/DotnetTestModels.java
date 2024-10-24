// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;
import software.amazon.polymorph.smithydafny.DafnyVersion;

class DotnetTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("AggregateReferences");
    DISABLED_TESTS.add("Documentation");
    DISABLED_TESTS.add("LanguageSpecificLogic");
    DISABLED_TESTS.add("LocalService");
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    // S3 is not yet supported
    DISABLED_TESTS.add("aws-sdks/s3");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  void testModelsForDotnet(String relativeTestModelPath) {
    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "polymorph_dafny");
    make(testModelPath, "polymorph_dotnet");
    make(testModelPath, "transpile_net");
    make(testModelPath, "test_net");
  }
}
