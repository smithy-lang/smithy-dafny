// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.conversion;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.TypeDescriptor;
import java.math.BigDecimal;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import java.nio.charset.StandardCharsets;
import java.time.Instant;
import java.util.ArrayList;
import java.util.Date;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * Methods that convert from a Dafny Runtime Type to native (natural) Java Type.<p>
 * Every Method here has its inverse is {@link ToDafny}.
 * @see <a href="https://dafny.org/dafny/DafnyRef/integration-java/IntegrationJava">Dafny Integration with Java</a>
 */
public class ToNative {

  /**
   * Methods that convert from a Dafny Runtime Type
   * to a native Java type,
   * for Smithy's definition of Simple shapes.
   * @see <a href="https://smithy.io/2.0/spec/simple-types.html#simple-types">Smithy Simple Types</a>
   */
  public static class Simple {

    /**
     * @param dafnySequence The Dafny Runtime type for a blob is a {@link DafnySequence} of {@link Byte}s.
     * @return The Java type for a blob can be a {@link ByteBuffer}.
     * @see ToDafny.Simple#ByteSequence
     */
    // BLOB("blob", BlobShape.class, Category.SIMPLE),
    public static ByteBuffer ByteBuffer(
      DafnySequence<? extends Byte> dafnySequence
    ) {
      return ByteBuffer.wrap((byte[]) dafnySequence.toRawArray());
    }

    /**
     * @param dafnySequence The Dafny Runtime type for a String is A {@link DafnySequence} of {@link Character}s.
     * @return The Java type for a String is {@link String}.
     * @see ToDafny.Simple#CharacterSequence
     */
    // STRING("string", StringShape.class, Category.SIMPLE),
    public static String String(
      DafnySequence<? extends Character> dafnySequence
    ) {
      Stream<? extends Character> chars = StreamSupport.stream(
        dafnySequence.spliterator(),
        false
      );
      return chars.map(Object::toString).collect(Collectors.joining());
    }

    /**
     * Deserialize the 8 Bytes from a {@link DafnySequence} of {@link Byte}s
     * into a {@link Double}.<p>
     * At this time,
     * Dafny does not have an idiomatic Double type
     * in the language or any standard library.<p>
     * As such, Doubles are represented as the serialized bytes of
     * their Native Type.<p>
     * Note: This serialization is NOT guaranteed to be
     * consistent among different Dafny Runtimes or
     * even native distributions.
     * @param dafnySequence A {@link DafnySequence} of 8 {@link Byte}s
     * @return The Java type for a double can be a {@link Double}.
     * @see ToDafny.Simple#Double
     */
    // DOUBLE("double", DoubleShape.class, Category.SIMPLE),
    public static Double Double(DafnySequence<? extends Byte> dafnySequence) {
      return ByteBuffer(dafnySequence).getDouble();
    }

    /**
     * Parse a {@link DafnySequence} of {@link Character}s into a {@link Date}.<p>
     * At this time, Dafny does not have an idiomatic Timestamp or Date type
     * in the language or any standard library.<p>
     * Instead, the Timestamp is serialized as seconds from epoch, as a string.
     * @param dafnySequence {@link DafnySequence} of {@link Character}s containing the serialization of the {@code timestamp}.
     * @return The Java type for a Smithy timestamp can be {@link Date}.
     * @see ToDafny.Simple#CharacterSequence(Date)
     */
    // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
    public static Date Date(DafnySequence<? extends Character> dafnySequence) {
      // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
      // Other services may use other formats
      BigDecimal dateValue = new BigDecimal(Simple.String(dafnySequence));
      return new Date(dateValue.scaleByPowerOfTen(3).longValue());
    }

    /**
     * Parse a {@link DafnySequence} of {@link Character}s into a {@link Instant}.<p>
     * At this time, Dafny does not have an idiomatic Timestamp or Date type
     * in the language or any standard library.<p>
     * Instead, the Timestamp is serialized as seconds from epoch, as a string.
     * @param dafnySequence {@link DafnySequence} of {@link Character}s containing the serialization of the {@code timestamp}.
     * @return The Java type for a Smithy timestamp can be {@link Instant}.
     * @see ToDafny.Simple#CharacterSequence(Instant)
     */
    // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
    public static Instant Instant(
      DafnySequence<? extends Character> dafnySequence
    ) {
      // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
      // Other services may use other formats
      BigDecimal dateValue = new BigDecimal(Simple.String(dafnySequence));
      return Instant.ofEpochMilli(dateValue.scaleByPowerOfTen(3).longValue());
    }

    /**
     * Decode a {@link DafnySequence} of UTF-8 {@link Byte}s into a {@link String}.
     * @param dafnySequence A {@link DafnySequence} of {@link Byte}s.
     * @return The Java type for a String is {@link String}
     * @see ToDafny.Simple#DafnyUtf8Bytes(String)
     */
    public static String DafnyUtf8Bytes(
      DafnySequence<? extends Byte> dafnySequence
    ) {
      Charset utf8 = StandardCharsets.UTF_8;
      // The only way to keep this thread/concurrent safe/ is
      // to create a new Coder everytime.
      // If we wanted to increase performance,
      // we could declare this NOT thread/concurrent safe,
      // and reset the coder everytime.
      CharsetDecoder coder = utf8.newDecoder();
      ByteBuffer inBuffer = ByteBuffer(dafnySequence);
      inBuffer.position(0);
      try {
        CharBuffer outBuffer = coder.decode(inBuffer);
        outBuffer.position(0);
        // Compared to the ByteBuffer in ToDafny.Simple.DafnyUtf8Bytes,
        // CharBuffer's toString is very user-friendly.
        // It appears to only read to the limit,
        // as compared to the capacity.
        return outBuffer.toString();
      } catch (CharacterCodingException ex) {
        throw new RuntimeException(
          "Could not encode input to Dafny Bytes.",
          ex
        );
      }
    }
  }

  /**
   * Methods that convert from a Dafny Runtime type
   * to a Native Java type,
   * for Smithy's definition of Aggregate shapes.
   * @see <a href="https://smithy.io/2.0/spec/aggregate-types.html#aggregate-types">Smithy Aggregate Types</a>
   */
  public static class Aggregate {

    /**
     * @param dafnyValues The Dafny Runtime Type for a List is a {@link DafnySequence}.
     * @param converter A {@link Function} that converts from a Dafny Runtime Type to a Native Java Type.
     * @param <T> The Dafny Runtime Type.
     * @param <R> The Native Java Type.
     * @return A {@link List} of {@code <R>},
     * which is the result of applying {@code converter} to
     * every member of {@code dafnyValues}.
     * @see ToDafny.Aggregate#GenericToSequence(List, Function, TypeDescriptor)
     */
    // LIST("list", ListShape.class, Category.AGGREGATE),
    public static <T, R> List<R> GenericToList(
      DafnySequence<T> dafnyValues,
      Function<T, R> converter
    ) {
      List<R> returnList = new ArrayList<>(dafnyValues.length());
      dafnyValues.forEach(value -> returnList.add(converter.apply(value)));
      return returnList;
    }

    /**
     * @param dafnyValues The Dafny Runtime Type for a Set is a {@link DafnySet}.
     * @param converter A {@link Function} that converts from a Dafny Runtime Type to a Native Java Type.
     * @param <T> The Dafny Runtime Type.
     * @param <R> The Native Java Type.
     * @return A {@link Set} of {@code <R>},
     * which is the result of applying {@code converter} to
     * every member of {@code dafnyValues}.
     * @see ToDafny.Aggregate#GenericToSet(Set, Function)
     */
    // SET("set", SetShape.class, Category.AGGREGATE),
    // technically, sets are deprecated in Smithy
    // They have been replaced with LIST w/ the uniqueItem trait
    public static <T, R> Set<R> GenericToSet(
      DafnySet<T> dafnyValues,
      Function<T, R> converter
    ) {
      // From the Smithy Docs:
      // "Implementations SHOULD use insertion ordered sets"
      // https://smithy.io/1.0/spec/core/model.html#set
      // Thus, we use a LinkedHashSet
      Set<R> returnSet = new LinkedHashSet<>(dafnyValues.size(), 1);
      dafnyValues
        .Elements()
        .forEach(value -> returnSet.add(converter.apply(value)));
      return returnSet;
    }

    /**
     * @param dafnyValues The Dafny Runtime type for a map can be {@link DafnyMap}.
     * @param keyConverter A {@link Function} that converts Dafny Runtime Type for the Key to a Native Java Type.
     * @param valueConverter A {@link Function} that converts Dafny Runtime Type for the Value to a Native Java Type.
     * @param <IN_KEY> The Dafny Runtime Type for the Key.
     * @param <IN_VALUE> The Dafny Runtime Type for the Value.
     * @param <OUT_KEY> The Native Java Type for the Key.
     * @param <OUT_VALUE> The Native Java Type for the Value.
     * @return A {@link Map} of {@code <OUT_KEY, OUT_VALUE>},
     * which is the result of applying {@code keyConverter} and {@code valueConverter} to
     * every member of {@code dafnyValues}.
     * @see ToDafny.Aggregate#GenericToMap(Map, Function, Function)
     */
    // MAP("map", MapShape.class, Category.AGGREGATE),
    // Technically, a smithy Map's Key value will always be a String
    public static <IN_KEY, IN_VALUE, OUT_KEY, OUT_VALUE> Map<
      OUT_KEY,
      OUT_VALUE
    > GenericToMap(
      DafnyMap<IN_KEY, IN_VALUE> dafnyValues,
      Function<IN_KEY, OUT_KEY> keyConverter,
      Function<IN_VALUE, OUT_VALUE> valueConverter
    ) {
      Map<OUT_KEY, OUT_VALUE> returnMap = new LinkedHashMap<>(
        dafnyValues.size(),
        1
      );
      dafnyValues.forEach((k, v) ->
        returnMap.put(keyConverter.apply(k), valueConverter.apply(v))
      );
      return returnMap;
    }
  }
}
