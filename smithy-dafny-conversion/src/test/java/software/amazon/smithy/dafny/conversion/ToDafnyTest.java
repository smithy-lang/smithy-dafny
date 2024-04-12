// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.conversion;

import static org.junit.Assert.assertEquals;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.TypeDescriptor;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ThreadLocalRandom;
import java.util.function.Function;
import java.util.stream.Collectors;
import org.junit.Test;

public class ToDafnyTest {

  private static final ArrayList<String> INPUT_LIST = new ArrayList<>();
  private static final String SMALL_STRING = "This is a string.";

  static {
    INPUT_LIST.add("Three");
    INPUT_LIST.add("Two");
    INPUT_LIST.add("One");
  }

  private static DafnySequence<
    ? extends DafnySequence<? extends Character>
  > ListString(List<String> list) {
    return ToDafny.Aggregate.GenericToSequence(
      list,
      ToDafny.Simple::CharacterSequence,
      DafnySequence._typeDescriptor(TypeDescriptor.CHAR)
    );
  }

  @Test
  public void testGenericToSequence() {
    ArrayList<String> input = (ArrayList<String>) INPUT_LIST.clone();
    class Local {

      public DafnySequence<? extends Character> ByIndex(BigInteger index) {
        return DafnySequence.asString(input.get(index.intValue()));
      }
    }
    Local local = new Local();
    DafnySequence<DafnySequence<? extends Character>> expected =
      DafnySequence.Create(
        DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
        BigInteger.valueOf(3),
        local::ByIndex
      );
    DafnySequence<? extends DafnySequence<? extends Character>> actual =
      ListString(input);
    assertEquals(expected, actual);
  }

  private static DafnySet<DafnySequence<? extends Character>> SetString(
    Set<String> set
  ) {
    return ToDafny.Aggregate.GenericToSet(
      set,
      ToDafny.Simple::CharacterSequence
    );
  }

  @Test
  public void testGenericToSet() {
    Set<String> input = new LinkedHashSet<>(
      (ArrayList<String>) INPUT_LIST.clone()
    );
    Set<DafnySequence<? extends Character>> temp = input
      .stream()
      .map(ToDafny.Simple::CharacterSequence)
      .collect(Collectors.toSet());
    @SuppressWarnings({ "unchecked", "rawtypes" })
    DafnySet expected = new DafnySet(temp);
    DafnySet<DafnySequence<? extends Character>> actual = SetString(input);
    assertEquals(expected, actual);
  }

  private static DafnyMap<
    DafnySequence<Character>,
    DafnySequence<Character>
  > MapStringString(Map<String, String> map) {
    return ToDafny.Aggregate.GenericToMap(
      map,
      ToDafny.Simple::CharacterSequence,
      ToDafny.Simple::CharacterSequence
    );
  }

  @Test
  public void testGenericToMap() {
    Map<DafnySequence<Character>, DafnySequence<Character>> temp =
      new LinkedHashMap<>();
    temp.put(DafnySequence.asString("one"), DafnySequence.asString("value"));
    temp.put(DafnySequence.asString("two"), DafnySequence.asString("value"));
    DafnyMap<DafnySequence<Character>, DafnySequence<Character>> expected =
      new DafnyMap<>(temp);
    Map<String, String> input = new LinkedHashMap<>();
    input.put("one", "value");
    input.put("two", "value");
    DafnyMap<DafnySequence<Character>, DafnySequence<Character>> actual =
      MapStringString(input);
    assertEquals(expected, actual);
  }

  private static DafnySet<Integer> SetInteger(Set<Integer> set) {
    return ToDafny.Aggregate.GenericToSet(set, Function.identity());
  }

  @Test
  public void testGenericToSetInteger() {
    Set<Integer> input = new LinkedHashSet<>(Arrays.asList(1, 2, 3));
    @SuppressWarnings({ "unchecked", "rawtypes" })
    DafnySet expected = new DafnySet(input);
    DafnySet<Integer> actual = SetInteger(input);
    assertEquals(expected, actual);
  }

  @Test
  public void testDafnyUtf8BytesSmall() {
    DafnySequence<Byte> actualDafny = ToDafny.Simple.DafnyUtf8Bytes(
      SMALL_STRING
    );
    assertEquals(17, actualDafny.length());
    String actualNative = ToNative.Simple.DafnyUtf8Bytes(actualDafny);
    assertEquals(SMALL_STRING, actualNative);
  }

  @Test
  public void testDafnyUtf8BytesDemo() throws IOException {
    // UTF-8-Demo.txt is written by Markus Kuhn
    // It was retrieved on 2022/12/11 from:
    // https://www.cl.cam.ac.uk/~mgk25/ucs/examples/UTF-8-demo.txt
    String expectedString = getResourceFileAsString("UTF-8-demo.txt");
    DafnySequence<Byte> actualDafny = ToDafny.Simple.DafnyUtf8Bytes(
      expectedString
    );
    String actualNative = ToNative.Simple.DafnyUtf8Bytes(actualDafny);
    assertEquals(expectedString, actualNative);
  }

  @Test
  public void testDafnyUtf8BytesLarge() throws IOException {
    // UTF-8-test.txt is written by Markus Kuhn
    // It was retrieved on 2022/12/10 from:
    // https://www.cl.cam.ac.uk/~mgk25/ucs/examples/UTF-8-test.txt
    String expectedString = getResourceFileAsString("UTF-8-test.txt");
    DafnySequence<Byte> actualDafny = ToDafny.Simple.DafnyUtf8Bytes(
      expectedString
    );
    String actualNative = ToNative.Simple.DafnyUtf8Bytes(actualDafny);
    assertEquals(expectedString, actualNative);
  }

  @Test
  public void testDouble() {
    for (int i = 0; i < 100; i++) {
      double random = ThreadLocalRandom.current().nextDouble();
      DafnySequence<Byte> actualDafny = ToDafny.Simple.Double(random);
      Double actualDouble = ToNative.Simple.Double(actualDafny);
      assertEquals((Double) random, actualDouble);
    }
  }

  /**
   * Reads given resource file as a string.
   *
   * @param fileName path to the resource file
   * @return the file's contents
   * @throws IOException if read fails for any reason
   *
   * @author
   * <a href="https://stackoverflow.com/a/46613809/2090045">Lucio Paiva</a>
   */
  static String getResourceFileAsString(String fileName) throws IOException {
    ClassLoader classLoader = ClassLoader.getSystemClassLoader();
    try (InputStream is = classLoader.getResourceAsStream(fileName)) {
      if (is == null) return null;
      try (
        InputStreamReader isr = new InputStreamReader(is);
        BufferedReader reader = new BufferedReader(isr)
      ) {
        return reader
          .lines()
          .collect(Collectors.joining(System.lineSeparator()));
      }
    }
  }
}
