// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.conversion;

import dafny.Array;
import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.Tuple2;
import dafny.TypeDescriptor;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.nio.CharBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.Charset;
import java.nio.charset.CharsetEncoder;
import java.nio.charset.StandardCharsets;
import java.time.Instant;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

/**
 * Methods that convert from a Native Java type to a Dafny Runtime type.<p>
 * Every Method here has its inverse is {@link ToNative}.
 * @see <a href="https://dafny.org/dafny/DafnyRef/integration-java/IntegrationJava">Dafny Integration with Java</a>
 */
public class ToDafny {

  /**
   * Methods that convert from a Native Java type
   * to a Dafny Java type,
   * for Smithy's definition of Simple shapes.
   * @see <a href="https://smithy.io/2.0/spec/simple-types.html#simple-types">Smithy Simple Types</a>
   */
  public static class Simple {

    /**
     * @param blob The Java type for a blob can be an array of bytes.
     * @return The Dafny Runtime type for a blob is a {@link DafnySequence} of {@link Byte}s.
     * @see ToNative.Simple#ByteBuffer
     */
    // BLOB("blob", BlobShape.class, Category.SIMPLE),
    public static DafnySequence<Byte> ByteSequence(byte[] blob) {
      return DafnySequence.fromArray(TypeDescriptor.BYTE, Array.wrap(blob));
    }

    /**
     * Copy {@code limit} bytes from {@code byteBuffer} starting at {@code start},
     * and return them as a Dafny Runtime {@link DafnySequence} of {@link Byte}s.
     * @param byteBuffer The Java type for a blob can be a {@link ByteBuffer}.
     * @param start The index in the byteBuffer from which to start at.
     * @param limit The number of bytes to copy.
     * @return A {@link DafnySequence} of {@link Byte}s, containing the copied bytes.
     * @see ToNative.Simple#ByteBuffer
     */
    // BLOB("blob", BlobShape.class, Category.SIMPLE),
    public static DafnySequence<Byte> ByteSequence(
      final ByteBuffer byteBuffer,
      final int start,
      final int limit
    ) {
      byte[] rawArray = new byte[limit - start];
      for (int i = 0; i < rawArray.length; i++) {
        rawArray[i] = byteBuffer.get(start + i);
      }
      return ByteSequence(rawArray);
    }

    /**
     * A convenience function for converting all the bytes from a ByteBuffer.
     * <p>
     * Note: Regardless of the buffer's mark, position, or capacity,
     * this will return the bytes from 0 till limit.
     *
     * @param byteBuffer The Java type for a blob can be a ByteBuffer.
     * @return A {@link DafnySequence} of {@link Byte}s,
     * containing the bytes in the {@code byteBuffer},
     * starting from 0 until the buffer's limit.
     * @see ToNative.Simple#ByteBuffer
     */
    // BLOB("blob", BlobShape.class, Category.SIMPLE),
    public static DafnySequence<Byte> ByteSequence(ByteBuffer byteBuffer) {
      return ByteSequence(byteBuffer, 0, byteBuffer.limit());
    }

    /**
     * At this time, Dafny does not have an idiomatic Double type in the language or any standard library.<p>
     * Instead, the Double is serialized into bytes,
     * which are then wrapped as a DafnySequence of Bytes.<p>
     * Note: This serialization is NOT guaranteed to be
     * consistent among different Dafny Runtimes or
     * even native distributions.
     * @param aDouble The Java type for a double can be a {@link Double}.
     * @return A {@link DafnySequence} of {@link Byte}s containing the serialization of the {@code aDouble}.
     * @see ToNative.Simple#Double
     */
    // DOUBLE("double", DoubleShape.class, Category.SIMPLE),
    public static DafnySequence<Byte> Double(Double aDouble) {
      ByteBuffer doubleBytes = ByteBuffer.allocate(8).putDouble(aDouble);
      return ByteSequence(doubleBytes, 0, 8);
    }

    /**
     * @param aString The Java type for a String is {@link String}.
     * @return The Dafny Runtime type for a String is A {@link DafnySequence} of {@link Character}s.
     * @see ToNative.Simple#String
     */
    // STRING("string", StringShape.class, Category.SIMPLE),
    public static DafnySequence<Character> CharacterSequence(String aString) {
      return DafnySequence.asString(aString);
    }

    /**
     * At this time, Dafny does not have an idiomatic Timestamp or Date type in the language or any standard library.<p>
     * Instead, the Timestamp is serialized as seconds from epoch, as a string,
     * which is than wrapped as a {@link DafnySequence} of {@link Character}s.
     * @param timestamp The Java type for a Smithy timestamp can be {@link Date}.
     * @return A {@link DafnySequence} of {@link Character}s containing the serialization of the {@code timestamp}.
     * @see ToNative.Simple#Date(DafnySequence)
     */
    // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
    public static DafnySequence<Character> CharacterSequence(Date timestamp) {
      // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
      // Other services may use other formats
      return CharacterSequence(
        String.format("%d", (timestamp.getTime() / 1000L))
      );
    }

    /**
     * At this time, Dafny does not have an idiomatic Timestamp or Date type in the language or any standard library.<p>
     * Instead, the Timestamp is serialized as seconds from epoch, as a string,
     * which is than wrapped as a DafnySequence of Charters.
     * @param timestamp The Java type for a timestamp can be {@link Instant}.
     * @return A {@link DafnySequence} of {@link Character}s containing the serialization of the {@code timestamp}.
     * @see ToNative.Simple#Instant(DafnySequence)
     */
    // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
    public static DafnySequence<Character> CharacterSequence(
      Instant timestamp
    ) {
      // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
      // Other services may use other formats
      return CharacterSequence(String.format("%d", timestamp.getEpochSecond()));
    }

    /**
     * Dafny can be configured to represent Strings in an encoding OTHER THAN UTF-8.<p>
     * (Until recently, it only supported UTF-16.)<p>
     * Regardless of how the Dafny Compiler is configured,
     * this method can be used to reliably convert a Java String
     * to a DafnySequence of UTF-8 Encoded bytes.
     * @param aString The Java type for a String is {@link String}
     * @return A {@link DafnySequence} of {@link Byte}s containing {@code aString} as UTF-8 Encoded Bytes.
     * @see ToNative.Simple#DafnyUtf8Bytes(DafnySequence)
     */
    public static DafnySequence<Byte> DafnyUtf8Bytes(String aString) {
      Charset utf8 = StandardCharsets.UTF_8;
      // The only way to keep this thread/concurrent safe/ is
      // to create a new Coder everytime.
      // If we wanted to increase performance,
      // we could declare this NOT thread/concurrent safe,
      // and reset the coder everytime.
      CharsetEncoder coder = utf8.newEncoder();
      CharBuffer inBuffer = CharBuffer.wrap(aString);
      inBuffer.position(0);
      try {
        ByteBuffer outBuffer = coder.encode(inBuffer);
        // outBuffer's capacity can be much higher than the limit.
        // By taking just the limit, we ensure we do not include
        // any allocated but un-filled space.
        return ByteSequence(outBuffer, 0, outBuffer.limit());
      } catch (CharacterCodingException ex) {
        throw new RuntimeException(
          "Could not encode input to Dafny Bytes.",
          ex
        );
      }
    }
  }

  /**
   * Methods that convert from a Native Java type
   * to a Dafny Runtime type,
   * for Smithy's definition of Aggregate shapes.
   * @see <a href="https://smithy.io/2.0/spec/aggregate-types.html#aggregate-types">Smithy Aggregate Types</a>
   */
  public static class Aggregate {

    /**
     * @param nativeValues The Java type for a list can be {@link List}.
     * @param converter A {@link Function} that converts from a natural Java Type to a Dafny Runtime Type.
     * @param typeDescriptor A {@link TypeDescriptor} that describes the Dafny Runtime Type.
     * @param <T> The natural Java Type.
     * @param <R> The Dafny Runtime Type.
     * @return A {@link DafnySequence} of {@code <R>},
     * which is the result of applying {@code converter} to
     * every member of {@code nativeValues}.
     * @see ToNative.Aggregate#GenericToList(DafnySequence, Function)
     */
    // LIST("list", ListShape.class, Category.AGGREGATE),
    public static <T, R> DafnySequence<? extends R> GenericToSequence(
      List<T> nativeValues,
      Function<T, R> converter,
      TypeDescriptor<R> typeDescriptor
    ) {
      return DafnySequence.Create(
        typeDescriptor,
        BigInteger.valueOf(nativeValues.size()),
        index -> converter.apply(nativeValues.get(index.intValue()))
      );
    }

    /**
     * Note: Sets in Java and in Dafny DO NOT preserve order; Smithy discourages un-ordered Sets.
     * @see <a href="https://smithy.io/1.0/spec/core/model.html#set">Simthy 1.0's Set</a>
     * @param nativeValues The Java type for a set can be {@link Set}.
     * @param converter A {@link Function} that converts from a natural Java Type to a Dafny Runtime Type.
     * @param <T> The natural Java Type.
     * @param <R> The Dafny Runtime Type.
     * @return A {@link DafnySet} of {@code <R>},
     * which is the result of applying {@code converter} to
     * every member of {@code nativeValues}.
     * @see ToNative.Aggregate#GenericToSet(DafnySet, Function)
     */
    // SET("set", SetShape.class, Category.AGGREGATE),
    // TODO: Frankly, we should avoid Dafny Sets since they do not preserve order;
    //  Smithy 2.0 deprecates Sets for Unique Lists to ensure order is preserved.
    // But, we would need to implement our own Dafny Ordered Set...
    public static <T, R> DafnySet<R> GenericToSet(
      Set<T> nativeValues,
      Function<T, R> converter
    ) {
      HashSet<R> hashSet = new HashSet<>(nativeValues.size(), 1);
      nativeValues.forEach(v -> hashSet.add(converter.apply(v)));
      return new DafnySet<>(hashSet);
    }

    /**
     * @param nativeValues The Java type for a map can be {@link Map}.
     * @param keyConverter A {@link Function} that converts natural Java Type for the Key to a Dafny Runtime Type.
     * @param valueConverter A {@link Function} that converts natural Java Type for the Value to a Dafny Runtime Type.
     * @param <IN_KEY> The natural Java Type for the Key
     * @param <IN_VALUE> The natural Java Type for the Value
     * @param <OUT_KEY> The Dafny Runtime Type for the Key.
     * @param <OUT_VALUE> The Dafny Runtime Type for the Value.
     * @return A {@link DafnyMap} of {@code <OUT_KEY, OUT_VALUE>},
     * which is the result of applying {@code keyConverter} and {@code valueConverter} to
     * every member of {@code nativeValues}.
     * @see ToNative.Aggregate#GenericToMap(DafnyMap, Function, Function)
     */
    // MAP("map", MapShape.class, Category.AGGREGATE),
    // Technically, a smithy Map's Key value will always be a String
    public static <IN_KEY, IN_VALUE, OUT_KEY, OUT_VALUE> DafnyMap<
      OUT_KEY,
      OUT_VALUE
    > GenericToMap(
      Map<IN_KEY, IN_VALUE> nativeValues,
      Function<IN_KEY, OUT_KEY> keyConverter,
      Function<IN_VALUE, OUT_VALUE> valueConverter
    ) {
      @SuppressWarnings("unchecked")
      Tuple2<OUT_KEY, OUT_VALUE>[] tuples = new Tuple2[nativeValues.size()];
      AtomicInteger counter = new AtomicInteger(0);
      nativeValues.forEach((k, v) ->
        tuples[counter.getAndIncrement()] =
          new Tuple2<>(keyConverter.apply(k), valueConverter.apply(v))
      );
      return DafnyMap.fromElements(tuples);
    }
  }
}
