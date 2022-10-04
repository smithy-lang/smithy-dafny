package software.amazon.dafny.conversion;

import org.junit.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.TypeDescriptor;

import static org.junit.Assert.assertEquals;

public class ToDafnyTest {
    private static final ArrayList<String> INPUT_LIST = new ArrayList<>();

    static {
        INPUT_LIST.add("Three");
        INPUT_LIST.add("Two");
        INPUT_LIST.add("One");
    }


    private static DafnySequence<? extends DafnySequence<? extends Character>> ListString(
            List<String> list
    ) {
        return ToDafny.Aggregate.GenericToSequence(list,
                ToDafny.Simple::CharacterSequence,
                DafnySequence._typeDescriptor(TypeDescriptor.CHAR));
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
        DafnySequence<DafnySequence<? extends Character>> expected = DafnySequence.Create(
                DafnySequence._typeDescriptor(TypeDescriptor.CHAR),
                BigInteger.valueOf(3),
                local::ByIndex
        );
        DafnySequence<? extends DafnySequence<? extends Character>> actual = ListString(input);
        assertEquals(expected, actual);
    }

    private static DafnySet<DafnySequence<? extends Character>> SetString(Set<String> set) {
        return ToDafny.Aggregate.GenericToSet(set, ToDafny.Simple::CharacterSequence);
    }

    @Test
    public void testGenericToSet() {
        Set<String> input = new LinkedHashSet<>((ArrayList<String>)INPUT_LIST.clone());
        Set<DafnySequence<? extends Character>> temp = input.stream().map(ToDafny.Simple::CharacterSequence).collect(Collectors.toSet());
        @SuppressWarnings({"unchecked", "rawtypes"})
        DafnySet expected = new DafnySet(temp);
        DafnySet<DafnySequence<? extends Character>> actual = SetString(input);
        assertEquals(expected, actual);
    }

    private static DafnyMap<DafnySequence<Character>, DafnySequence<Character>> MapStringString(Map<String,String> map) {
        return ToDafny.Aggregate.GenericToMap(map,
                ToDafny.Simple::CharacterSequence,
                ToDafny.Simple::CharacterSequence);
    }

    @Test
    public void testGenericToMap() {
        Map<DafnySequence<Character>, DafnySequence<Character>> temp = new LinkedHashMap<>();
        temp.put(DafnySequence.asString("one"), DafnySequence.asString("value"));
        temp.put(DafnySequence.asString("two"), DafnySequence.asString("value"));
        DafnyMap<DafnySequence<Character>, DafnySequence<Character>> expected = new DafnyMap<>(temp);
        Map<String,String> input = new LinkedHashMap<>();
        input.put("one", "value");
        input.put("two", "value");
        DafnyMap<DafnySequence<Character>, DafnySequence<Character>> actual = MapStringString(input);
        assertEquals(expected, actual);
    }


    private static DafnySet<Integer> SetInteger(Set<Integer> set) {
        return ToDafny.Aggregate.GenericToSet(set, Function.identity());
    }

    @Test
    public void testGenericToSetInteger() {
        Set<Integer> input = new LinkedHashSet<>(Arrays.asList(1, 2, 3));
        @SuppressWarnings({"unchecked", "rawtypes"})
        DafnySet expected = new DafnySet(input);
        DafnySet<Integer> actual = SetInteger(input);
        assertEquals(expected, actual);
    }
}
