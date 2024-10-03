// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import java.util.Arrays;
import java.util.Collection;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import software.amazon.polymorph.smithydafny.DafnyVersion;

@RunWith(Parameterized.class)
public abstract class ForEachDafnyTest {

  @Parameterized.Parameters(name = "dafnyVersion = {0}")
  public static Collection dafnies() {
    return Arrays.asList(new Object[][] { { new DafnyVersion(4, 8, 0) } });
  }
}
