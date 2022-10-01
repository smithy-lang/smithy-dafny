package software.amazon.polymorph.smithyjava.common;

import com.squareup.javapoet.JavaFile;

import org.junit.Test;

import static org.junit.Assert.assertNotNull;

/**
 * <p>Static Errors are the Polymorph specific errors that all
 * generated modules need but are not modeled in the smithy model.
 */
public class StaticErrorsTest {
    static String packageName = "software.amazon.cryptography.model";

    @Test
    public void NativeErrorTest() {
        JavaFile actual = NativeError.javaFile(packageName);
        String actualString = actual.toString();
        //TODO: actually test something
        assertNotNull(actualString);
    }

    @Test
    public void OpaqueErrorTest() {
        JavaFile actual = OpaqueError.javaFile(packageName);
        String actualString = actual.toString();
        //TODO: actually test something
        assertNotNull(actualString);
    }

    @Test
    public void CollectionErrorTest() {
        JavaFile actual = CollectionOfErrors.javaFile(packageName);
        String actualString = actual.toString();
        //TODO: actually test something
        assertNotNull(actualString);
    }

}
