// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import static software.amazon.smithy.dafny.codegen.TestUtils.make;

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
    // Needs work to generate some missing orphaned shape conversion methods
    DISABLED_TESTS.add("OrphanedShapes");
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleDocument");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    DISABLED_TESTS.add("aws-sdks/ddb-lite");
    DISABLED_TESTS.add("aws-sdks/glue");
    DISABLED_TESTS.add("aws-sdks/lakeformation");
    DISABLED_TESTS.add("aws-sdks/kms-lite");
    DISABLED_TESTS.add("aws-sdks/sqs");
    DISABLED_TESTS.add("aws-sdks/sqs-via-cli");
    DISABLED_TESTS.add("aws-sdks/s3");
    DISABLED_TESTS.add("Streaming");
    DISABLED_TESTS.add("SQSExtended");
    //TODO: We should be able to support below models, but isn't a priority.
    DISABLED_TESTS.add("MultipleModels");
    DISABLED_TESTS.add("LocalService");

    //V1 Tests are not supported in Go
    DISABLED_TESTS.add("aws-sdks/ddb");
    DISABLED_TESTS.add("aws-sdks/kms");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  protected void testModels(String relativeTestModelPath) {
    super.testModels(relativeTestModelPath);

    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    // Order is important here otherwise we might run into formatting issues.
    make(testModelPath, "setup_prettier");
    make(testModelPath, "polymorph_dafny");
    make(testModelPath, "transpile_go");
    make(testModelPath, "polymorph_go");
    //TODO: Remove this TODO line once run_goimports TODO in SmithyDafnyMakefile is fixed.
    make(testModelPath, "run_goimports");
    make(testModelPath, "test_go");
  }
}
