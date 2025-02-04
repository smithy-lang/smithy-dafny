// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithyrust;

import static software.amazon.smithy.dafny.codegen.TestUtils.make;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

class RustTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("AggregateReferences");
    DISABLED_TESTS.add("CodegenPatches");
    DISABLED_TESTS.add("Dependencies");
    DISABLED_TESTS.add("Extern");
    DISABLED_TESTS.add("LanguageSpecificLogic");
    DISABLED_TESTS.add("Refinement");
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleDocument");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    DISABLED_TESTS.add("Streaming");
    DISABLED_TESTS.add("SQSExtended");
    DISABLED_TESTS.add("aws-sdks/glue");
    DISABLED_TESTS.add("aws-sdks/lakeformation");
    DISABLED_TESTS.add("aws-sdks/sqs");
    DISABLED_TESTS.add("aws-sdks/sqs-via-cli");
    //TODO: Add support for Recursive shapes.
    DISABLED_TESTS.add("RecursiveShape");
    // S3 is not yet supported
    DISABLED_TESTS.add("aws-sdks/s3");

    //TODO: https://github.com/smithy-lang/smithy-dafny/issues/599
    DISABLED_TESTS.add("Positional");

    //TODO: https://github.com/smithy-lang/smithy-dafny/issues/699
    DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  void testModelsForRust(String relativeTestModelPath) {
    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "polymorph_dafny");
    // Note we transpile first because we're currently patching
    // the Dafny-generated code as well.
    make(testModelPath, "transpile_rust");
    make(testModelPath, "polymorph_rust");
    make(testModelPath, "test_rust");
    // Since we're checking in generated (or benerated) code,
    // make sure the state matches what's checked in.
    make(testModelPath, "check_polymorph_diff");
  }
}
