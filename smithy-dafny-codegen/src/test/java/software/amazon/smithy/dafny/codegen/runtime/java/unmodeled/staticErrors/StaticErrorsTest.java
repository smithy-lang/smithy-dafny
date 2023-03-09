package software.amazon.smithy.dafny.codegen.runtime.java.unmodeled.staticErrors;

import com.squareup.javapoet.JavaFile;

import org.junit.Test;

import software.amazon.smithy.dafny.codegen.runtime.java.unmodeled.CollectionOfErrors;
import software.amazon.smithy.dafny.codegen.runtime.java.unmodeled.NativeError;
import software.amazon.smithy.dafny.codegen.runtime.java.unmodeled.OpaqueError;

import static software.amazon.smithy.dafny.codegen.util.Tokenizer.tokenizeAndAssertEqual;

/**
 * <p>Static Errors are the Polymorph specific errors that all
 * generated modules need but are not modeled in the smithy model.
 */
//TODO: Refactor to test components instead of whole
public class StaticErrorsTest {
    static String packageName = "software.amazon.cryptography.model";

    @Test
    public void NativeErrorTest() {
        JavaFile actual = NativeError.javaFile(packageName);
        String actualString = actual.toString();
        tokenizeAndAssertEqual(Constants.NATIVE_ERROR_EXPECTED, actualString);
    }

    @Test
    public void OpaqueErrorTest() {
        JavaFile actual = OpaqueError.javaFile(packageName);
        String actualString = actual.toString();
        tokenizeAndAssertEqual(Constants.OPAQUE_ERROR_EXPECTED, actualString);
    }

    @Test
    public void CollectionErrorTest() {
        JavaFile actual = CollectionOfErrors.javaFile(packageName);
        String actualString = actual.toString();
        tokenizeAndAssertEqual(Constants.COLLECTION_ERROR_EXPECTED, actualString);
    }

}
