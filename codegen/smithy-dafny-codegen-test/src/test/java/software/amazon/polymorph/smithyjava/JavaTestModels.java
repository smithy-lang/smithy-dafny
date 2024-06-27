package software.amazon.polymorph.smithyjava;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import software.amazon.polymorph.TestModelTest;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.Set;

class JavaTestModels extends TestModelTest {

    private static final Set<String> DISABLED_TESTS = new HashSet<>();
    static {
        DISABLED_TESTS.add("Aggregate");
        DISABLED_TESTS.add("AggregateReferences");
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
        DISABLED_TESTS.add("SimpleTypes/SimpleDouble");
        DISABLED_TESTS.add("SimpleTypes/SimpleEnum");
        DISABLED_TESTS.add("SimpleTypes/SimpleEnumV2");
        DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
        DISABLED_TESTS.add("SimpleTypes/SimpleInteger");
        DISABLED_TESTS.add("SimpleTypes/SimpleLong");
        DISABLED_TESTS.add("SimpleTypes/SimpleShort");
        DISABLED_TESTS.add("SimpleTypes/SimpleString");
        DISABLED_TESTS.add("SimpleTypes/SimpleTimestamp");
        DISABLED_TESTS.add("SimpleTypes/Union");
    }

    @ParameterizedTest
    @MethodSource("discoverTestModels")
    void testModelsForDotnet(String relativeTestModelPath) {
        Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

        Path testModelPath = getTestModelPath(relativeTestModelPath);
        make(testModelPath, "setup_prettier");
        make(testModelPath, "polymorph_dafny");
        make(testModelPath, "polymorph_java");
        make(testModelPath, "transpile_java");
        make(testModelPath, "test_java");
    }
}