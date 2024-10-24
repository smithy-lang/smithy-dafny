// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

class PythonTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("AggregateReferences");
    DISABLED_TESTS.add("CallingAWSSDKFromLocalService");
    DISABLED_TESTS.add("LanguageSpecificLogic");
    DISABLED_TESTS.add("MultipleModels");
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp");
    DISABLED_TESTS.add("aws-sdks/ddb-lite");
    DISABLED_TESTS.add("aws-sdks/glue");
    DISABLED_TESTS.add("aws-sdks/lakeformation");
    DISABLED_TESTS.add("aws-sdks/kms-lite");
    DISABLED_TESTS.add("aws-sdks/sqs");
    DISABLED_TESTS.add("aws-sdks/sqs-via-cli");
    //TODO: Add support for Recursive shapes.
    DISABLED_TESTS.add("RecursiveShape");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  void testModelsForPython(String relativeTestModelPath) {
    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "setup_prettier");
    make(testModelPath, "polymorph_dafny");
    make(testModelPath, "polymorph_python");
    make(testModelPath, "transpile_python");
    make(testModelPath, "test_python");
  }
}
