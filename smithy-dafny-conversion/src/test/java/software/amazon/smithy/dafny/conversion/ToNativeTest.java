// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.conversion;

import static org.junit.Assert.assertEquals;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import org.junit.Test;

public class ToNativeTest {

  private static final ArrayList<String> INPUT_LIST = new ArrayList<>();

  static {
    INPUT_LIST.add("Three");
    INPUT_LIST.add("Two");
    INPUT_LIST.add("One");
  }

  private static List<String> ListString(
    DafnySequence<DafnySequence<? extends Character>> seq
  ) {
    return ToNative.Aggregate.GenericToList(seq, ToNative.Simple::String);
  }

  @Test
  public void testGenericToList() {
    List<String> expected = (ArrayList<String>) INPUT_LIST.clone();
    class Local {

      public DafnySequence<? extends Character> ByIndex(BigInteger index) {
        return DafnySequence.asString(expected.get(index.intValue()));
      }
    }
    Local local = new Local();
    DafnySequence<DafnySequence<? extends Character>> input =
      DafnySequence.Create(
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
        BigInteger.valueOf(3),
        local::ByIndex
      );
    List<? extends String> actual = ListString(input);
    assertEquals(expected, actual);
  }

  private static Set<String> SetString(
    DafnySet<DafnySequence<? extends Character>> set
  ) {
    return ToNative.Aggregate.GenericToSet(set, ToNative.Simple::String);
  }

  @Test
  public void testGenericToSet() {
    Set<String> expected = new LinkedHashSet<>(
      (ArrayList<String>) INPUT_LIST.clone()
    );
    Set<DafnySequence<? extends Character>> temp = expected
      .stream()
      .map(ToDafny.Simple::CharacterSequence)
      .collect(Collectors.toSet());
    DafnySet<DafnySequence<? extends Character>> input = new DafnySet<>(temp);
    Set<String> actual = SetString(input);
    assertEquals(expected, actual);
  }

  private static Map<String, String> MapStringString(
    DafnyMap<
      DafnySequence<? extends Character>,
      DafnySequence<? extends Character>
    > map
  ) {
    return ToNative.Aggregate.GenericToMap(
      map,
      ToNative.Simple::String,
      ToNative.Simple::String
    );
  }

  @Test
  public void testGenericToMap() {
    Map<String, String> expected = new LinkedHashMap<>();
    expected.put("one", "value");
    expected.put("two", "value");
    Map<
      DafnySequence<? extends Character>,
      DafnySequence<? extends Character>
    > temp = new LinkedHashMap<>();
    temp.put(DafnySequence.asString("one"), DafnySequence.asString("value"));
    temp.put(DafnySequence.asString("two"), DafnySequence.asString("value"));
    DafnyMap<
      DafnySequence<? extends Character>,
      DafnySequence<? extends Character>
    > input = new DafnyMap<>(temp);
    Map<String, String> actual = MapStringString(input);
    assertEquals(expected, actual);
  }
}
