package software.amazon.polymorph.smithyjava;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public abstract class ForEachDafnyTest {

    @Parameterized.Parameters(name = "dafnyVersion = {0}")
    public static Collection dafnies() {
        return Arrays.asList(new Object[][] {
                { "4.1" },
                { "4.3" },
        });
    }
}
