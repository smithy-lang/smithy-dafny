package software.amazon.polymorph.smithyjava.unmodeled.staticErrors;

import com.squareup.javapoet.JavaFile;

import org.junit.Test;

import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;

import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

/**
 * <p>Static Errors are the Polymorph specific errors that all
 * generated modules need but are not modeled in the smithy model.
 */
//TODO: Refactor to test components instead of whole
public class StaticErrorsTest {
    static String packageName = "software.amazon.cryptography.model";

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
