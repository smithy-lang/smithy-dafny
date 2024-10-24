// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

class GoTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("AggregateReferences");
    DISABLED_TESTS.add("Documentation");
    DISABLED_TESTS.add("LanguageSpecificLogic");
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
    //TODO: We should ne able to support below models.
    DISABLED_TESTS.add("MultipleModels");
    DISABLED_TESTS.add("LocalService");

    //TODO: Pending PR Merge
    DISABLED_TESTS.add("Positional");

    //TODO: Fix this before main merge
    DISABLED_TESTS.add("Dependencies");

    //V1 Tests are not supported in Go
    DISABLED_TESTS.add("aws-sdks/ddb");
    DISABLED_TESTS.add("aws-sdks/kms");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  void testModelsForGo(final String relativeTestModelPath) {
    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "setup_prettier");
    make(testModelPath, "polymorph_dafny");
    make(testModelPath, "polymorph_go");
    make(testModelPath, "transpile_go");
    make(testModelPath, "test_go");
  }
}
