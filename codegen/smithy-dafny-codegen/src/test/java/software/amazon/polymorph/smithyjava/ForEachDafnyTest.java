// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import software.amazon.polymorph.smithydafny.DafnyVersion;

import java.util.Arrays;
import java.util.Collection;

@RunWith(Parameterized.class)
public abstract class ForEachDafnyTest {

    @Parameterized.Parameters(name = "dafnyVersion = {0}")
    public static Collection dafnies() {
        return Arrays.asList(new Object[][] {
                { new DafnyVersion(4, 1, 0) },
                { new DafnyVersion(4, 3, 0) },
        });
    }
}
