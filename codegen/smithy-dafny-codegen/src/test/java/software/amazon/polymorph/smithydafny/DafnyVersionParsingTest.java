// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithydafny;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;

@RunWith(Parameterized.class)
public class DafnyVersionParsingTest {

  public DafnyVersionParsingTest(String versionString, DafnyVersion expected) {
    this.versionString = versionString;
    this.expected = expected;
  }

  @Parameterized.Parameters(name = "{0} ==> {1}")
  public static Collection data() {
    return Arrays.asList(
      new Object[][] {
        // Valid
        { "4", new DafnyVersion(4, 0, 0) },
        { "4.1", new DafnyVersion(4, 1, 0) },
        { "4.1.4", new DafnyVersion(4, 1, 4) },
        { "4-almost", new DafnyVersion(4, 0, 0, "almost") },
        { "4.1-beta", new DafnyVersion(4, 1, 0, "beta") },
        { "4.1.4-any-day-now", new DafnyVersion(4, 1, 4, "any-day-now") },
        // Invalid
        { "", null },
        { "$@%!", null },
        { "1.2.3.4", null },
        { "not.even.numbers", null },
      }
    );
  }

  private final String versionString;
  private final DafnyVersion expected;

  @Test
  public void testParsing() {
    try {
      DafnyVersion parsed = DafnyVersion.parse(versionString);
      assertEquals(expected, parsed);
    } catch (IllegalArgumentException e) {
      assertEquals(null, expected);
    }
  }
}
