// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithyrust;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;

class RustTestModels extends TestModelTest {

    private static final Set<String> DISABLED_TESTS = new HashSet<>();
    static {
        DISABLED_TESTS.add("AggregateReferences");
        DISABLED_TESTS.add("CodegenPatches");
        DISABLED_TESTS.add("Constraints");
        DISABLED_TESTS.add("Constructor");
        DISABLED_TESTS.add("Dependencies");
        DISABLED_TESTS.add("Errors");
        DISABLED_TESTS.add("CodegenPatches");
        DISABLED_TESTS.add("Extendable");
        DISABLED_TESTS.add("Extern");
        DISABLED_TESTS.add("LanguageSpecificLogic");
        DISABLED_TESTS.add("LocalService");
        DISABLED_TESTS.add("MultipleModels");
        DISABLED_TESTS.add("SimpleTypes/BigDecimal");
        DISABLED_TESTS.add("SimpleTypes/BigInteger");
        DISABLED_TESTS.add("SimpleTypes/SimpleByte");
        DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
        DISABLED_TESTS.add("SimpleTypes/SimpleShort");
        DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp");
        DISABLED_TESTS.add("aws-sdks/ddb");
        DISABLED_TESTS.add("aws-sdks/glue");
        DISABLED_TESTS.add("aws-sdks/lakeformation");
        DISABLED_TESTS.add("aws-sdks/kms");
        DISABLED_TESTS.add("aws-sdks/sqs");
        DISABLED_TESTS.add("aws-sdks/sqs-via-cli");
    }

    @ParameterizedTest
    @MethodSource("discoverTestModels")
    void testModelsForDotnet(String relativeTestModelPath) {
        Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

        Path testModelPath = getTestModelPath(relativeTestModelPath);
        make(testModelPath, "polymorph_dafny");
        // Note we transpile first because we're currently patching
        // the Dafny-generated code as well.
        make(testModelPath, "transpile_rust");
        make(testModelPath, "polymorph_rust");
        make(testModelPath, "test_rust");
        // Since we're checking in and patching code,
        // make sure the patch files are up to date.
        make(testModelPath, "check_polymorph_diff");
    }
}