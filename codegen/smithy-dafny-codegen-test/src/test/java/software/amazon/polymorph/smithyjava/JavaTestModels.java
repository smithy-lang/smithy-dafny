// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithyjava;

import static software.amazon.smithy.dafny.codegen.TestUtils.make;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.TestModelTest;
import software.amazon.polymorph.smithydafny.DafnyVersion;

class JavaTestModels extends TestModelTest {

  private static final Set<String> DISABLED_TESTS = new HashSet<>();

  static {
    DISABLED_TESTS.add("Aggregate");
    DISABLED_TESTS.add("AggregateReferences");
    DISABLED_TESTS.add("CallingAWSSDKFromLocalService");
    DISABLED_TESTS.add("Constructor");
    DISABLED_TESTS.add("Dependencies");
    DISABLED_TESTS.add("Extern");
    DISABLED_TESTS.add("LanguageSpecificLogic");
    DISABLED_TESTS.add("Refinement");
    DISABLED_TESTS.add("SimpleTypes/BigDecimal");
    DISABLED_TESTS.add("SimpleTypes/BigInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleBlob");
    DISABLED_TESTS.add("SimpleTypes/SimpleBoolean");
    DISABLED_TESTS.add("SimpleTypes/SimpleByte");
    DISABLED_TESTS.add("SimpleTypes/SimpleDocument");
    DISABLED_TESTS.add("SimpleTypes/SimpleDouble");
    DISABLED_TESTS.add("SimpleTypes/SimpleEnum");
    DISABLED_TESTS.add("SimpleTypes/SimpleEnumV2");
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
    DISABLED_TESTS.add("SimpleTypes/SimpleInteger");
    DISABLED_TESTS.add("SimpleTypes/SimpleLong");
    DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    DISABLED_TESTS.add("SimpleTypes/SimpleString");
    DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp");
    DISABLED_TESTS.add("Streaming");
    DISABLED_TESTS.add("Union");
    DISABLED_TESTS.add("aws-sdks/kms-lite");
    DISABLED_TESTS.add("aws-sdks/sqs");
    DISABLED_TESTS.add("aws-sdks/sqs-via-cli");
    //TODO: Add support for Recursive shapes.
    DISABLED_TESTS.add("RecursiveShape");
    // S3 is not yet supported
    DISABLED_TESTS.add("aws-sdks/s3");

    //TODO: https://github.com/smithy-lang/smithy-dafny/issues/599
    DISABLED_TESTS.add("Positional");
  }

  @ParameterizedTest
  @MethodSource("discoverTestModels")
  protected void testModels(String relativeTestModelPath) {
    super.testModels(relativeTestModelPath);

    // This test is hacked up to pass for Java in a way that doesn't work
    // for older Dafny versions.
    if (relativeTestModelPath.endsWith("Constraints")) {
      DafnyVersion dafnyVersion = CodegenEngine.getDafnyVersionFromDafny();
      if (dafnyVersion.compareTo(DafnyVersion.parse("4.9.0")) < 0) {
        Assumptions.assumeTrue(false);
      }
    }

    Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

    Path testModelPath = getTestModelPath(relativeTestModelPath);
    make(testModelPath, "setup_prettier");
    make(testModelPath, "polymorph_dafny");
    make(testModelPath, "polymorph_java");
    make(testModelPath, "transpile_java");
    make(testModelPath, "build_java");
    make(testModelPath, "test_java");
  }
}
