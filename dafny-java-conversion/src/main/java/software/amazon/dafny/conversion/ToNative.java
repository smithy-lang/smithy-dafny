package software.amazon.dafny.conversion;

import java.math.BigDecimal;
import java.nio.ByteBuffer;
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

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;

public class ToNative {

    /**
     * Methods that convert from a Dafny generated Java type
     * to a native Java type,
     * for Smithy's definition of Simple shapes.
     */
    public static class Simple {

        // BLOB("blob", BlobShape.class, Category.SIMPLE),
        static public ByteBuffer ByteBuffer(DafnySequence<? extends Byte> dafnySequence) {
            return ByteBuffer.wrap((byte[]) dafnySequence.toRawArray());
        }

        // STRING("string", StringShape.class, Category.SIMPLE),
        public static String String(DafnySequence<? extends Character> s) {
            Stream<? extends Character> chars = StreamSupport.stream(s.spliterator(), false);
            return chars.map(Object::toString).collect(Collectors.joining());
        }

        // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
        public static Date Date(DafnySequence<? extends Character> s) {
            // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
            // Other services may use other formats
            BigDecimal dateValue = new BigDecimal(Simple.String(s));
            return new Date(dateValue.scaleByPowerOfTen(3).longValue());
        }

        // TIMESTAMP("timestamp", TimestampShape.class, Category.SIMPLE),
        public static Instant Instant(DafnySequence<? extends Character> s) {
            // KMS uses unix timestamp, or seconds from epoch, as its serialized timestamp
            // Other services may use other formats
            BigDecimal dateValue = new BigDecimal(Simple.String(s));
            return Instant.ofEpochMilli(dateValue.scaleByPowerOfTen(3).longValue());
        }
    }

    public static class Aggregate {
        // LIST("list", ListShape.class, Category.AGGREGATE),
        public static <INPUT, OUTPUT> List<OUTPUT> GenericToList(
                DafnySequence<INPUT> dafnyValues,
                Function<INPUT, OUTPUT> converter
        ) {
            List<OUTPUT> returnList = new ArrayList<>(dafnyValues.length());
            dafnyValues.forEach(value ->
                    returnList.add(converter.apply(value))
            );
            return returnList;
        }

        // SET("set", SetShape.class, Category.AGGREGATE),
        // technically, sets are deprecated in Smithy
        // They have been replaced with LIST w/ the uniqueItem trait
        public static <INPUT, OUTPUT> Set<OUTPUT> GenericToSet(
                DafnySet<INPUT> dafnyValues,
                Function<INPUT, OUTPUT> converter
        ) {
            // From the Smithy Docs:
            // "Implementations SHOULD use insertion ordered sets"
            // https://awslabs.github.io/smithy/1.0/spec/core/model.html#set
            // Thus, we use a LinkedHashSet
            Set<OUTPUT> returnSet = new LinkedHashSet<>(dafnyValues.size(), 1);
            dafnyValues.Elements().forEach(value ->
                    returnSet.add(converter.apply(value))
            );
            return returnSet;
        }

        // MAP("map", MapShape.class, Category.AGGREGATE),
        // Technically, a smithy Map's Key value will always be a String
        public static <IN_KEY, IN_VALUE, OUT_KEY, OUT_VALUE> Map<OUT_KEY, OUT_VALUE> GenericToMap(
                DafnyMap<IN_KEY, IN_VALUE> dafnyValues,
                Function<IN_KEY, OUT_KEY> keyConverter,
                Function<IN_VALUE, OUT_VALUE> valueConverter
        ) {
            Map<OUT_KEY, OUT_VALUE> returnMap = new LinkedHashMap<>(dafnyValues.size(), 1);
            dafnyValues.forEach((k, v) ->
                    returnMap.put(keyConverter.apply(k), valueConverter.apply(v)));
            return returnMap;
        }
    }
}
