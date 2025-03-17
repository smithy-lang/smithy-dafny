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

    DISABLED_TESTS.add("Dependencies"); // Smithy-Dafny Error

    DISABLED_TESTS.add("Extern");

    DISABLED_TESTS.add("LanguageSpecificLogic"); // Smithy-Dafny Error
    DISABLED_TESTS.add("Positional"); // Smithy-Dafny Error
    DISABLED_TESTS.add("Refinement"); // Smithy-Dafny Error
    DISABLED_TESTS.add("SimpleTypes/SimpleBoolean"); // Need runtime
    DISABLED_TESTS.add("SimpleTypes/SimpleDouble"); // Error in generated type conversion
    DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp"); // Need to add for Java

    DISABLED_TESTS.add("aws-sdks/kms-lite"); // Not written yet
    DISABLED_TESTS.add("aws-sdks/s3"); // Not written yet
    DISABLED_TESTS.add("aws-sdks/sqs"); // Not written yet
    DISABLED_TESTS.add("aws-sdks/sqs-via-cli"); // Not written yet

    DISABLED_TESTS.add("AggregateReferences"); // Not supported yet
    DISABLED_TESTS.add("RecursiveShape"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/BigDecimal"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/BigInteger"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/SimpleByte"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/SimpleDocument"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/SimpleFloat"); // Not supported yet
    DISABLED_TESTS.add("SimpleTypes/SimpleShort"); // Not supported yet
    DISABLED_TESTS.add("Streaming"); // Not supported yet
    //    These are commented out because they should work
    //    They are left here because it can be useful
    //    to have these here so that it is easy to only run a single test locally.
    //    DISABLED_TESTS.add("CallingAWSSDKFromLocalService"); // These work
    //    DISABLED_TESTS.add("CodegenPatches"); // These work
    //    DISABLED_TESTS.add("Constraints"); // These work
    //    DISABLED_TESTS.add("Constructor"); // These work
    //    DISABLED_TESTS.add("Documentation"); // These work
    //    DISABLED_TESTS.add("Errors"); // These work
    //    DISABLED_TESTS.add("Extendable"); // These work
    //    DISABLED_TESTS.add("LocalService"); // These work
    //    DISABLED_TESTS.add("MultipleModels"); // These work
    //    DISABLED_TESTS.add("OrphanedShapes"); // These work
    //    DISABLED_TESTS.add("Resource"); // These work
    //    DISABLED_TESTS.add("SQSExtended"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleBlob"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleEnum"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleEnumV2"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleInteger"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleLong"); // These work
    //    DISABLED_TESTS.add("SimpleTypes/SimpleString"); // These work
    //    DISABLED_TESTS.add("Union"); // These work
    //    DISABLED_TESTS.add("aws-sdks/ddb"); // These work
    //    DISABLED_TESTS.add("aws-sdks/ddb-lite"); // These work
    //    DISABLED_TESTS.add("aws-sdks/ddbv2"); // These work
    //    DISABLED_TESTS.add("aws-sdks/glue"); // These work
    //    DISABLED_TESTS.add("aws-sdks/kms"); // These work
    //    DISABLED_TESTS.add("aws-sdks/kmsv2"); // These work
    //    DISABLED_TESTS.add("aws-sdks/lakeformation"); // These work
    //    DISABLED_TESTS.add("dafny-dependencies/StandardLibrary"); // These work
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
    make(testModelPath, "build_java");
    make(testModelPath, "test_java");
  }
}
