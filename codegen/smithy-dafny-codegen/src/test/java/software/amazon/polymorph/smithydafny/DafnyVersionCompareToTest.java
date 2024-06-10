// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithydafny;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class DafnyVersionCompareToTest {

  @Parameterized.Parameters(name = "{0} compareTo {1} == {2}")
  public static Collection data() {
    return Arrays.asList(
      new Object[][] {
        { "4.1", "4", 1 },
        { "4.0", "4", 0 },
        { "4", "4.0.0", 0 },
        { "4.1.3", "4", 1 },
        { "3.11", "4", -1 },
        { "4.1", "4", 1 },
        { "4.1.1", "4.1.2", -1 },
        { "4.1.1", "4.1.1", 0 },
        { "4.1.2", "4.1.1", 1 },
        { "4-alpha", "4", -1 },
        { "4-alpha", "4.0", -1 },
        { "4-alpha", "4-alpha", 0 },
        { "4-alpha", "4-beta", -1 },
      }
    );
  }

  public DafnyVersionCompareToTest(String lhs, String rhs, int expected) {
    this.lhs = lhs;
    this.rhs = rhs;
    this.expected = expected;
  }

  private final String lhs;
  private final String rhs;
  private final int expected;

  @Test
  public void testCompareTo() {
    DafnyVersion left = DafnyVersion.parse(lhs);
    DafnyVersion right = DafnyVersion.parse(rhs);
    assertEquals(expected, left.compareTo(right));
  }
}
