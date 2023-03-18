// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static boolean IsValid__BlobLessThanOrEqualToTen(dafny.DafnySequence<? extends Byte> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0;
  }
  public static boolean IsValid__GreaterThanOne(int x) {
    return (1) <= (x);
  }
  public static boolean IsValid__LessThanTen(int x) {
    return (x) <= (10);
  }
  public static boolean IsValid__ListLessThanOrEqualToTen(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0;
  }
  public static boolean IsValid__MapLessThanOrEqualToTen(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.valueOf((x).size())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0;
  }
  public static boolean IsValid__MyBlob(dafny.DafnySequence<? extends Byte> x) {
    return ((java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0);
  }
  public static boolean IsValid__MyList(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return ((java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0);
  }
  public static boolean IsValid__MyMap(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return ((java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).size()))) <= 0) && ((java.math.BigInteger.valueOf((x).size())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0);
  }
  public static boolean IsValid__MyString(dafny.DafnySequence<? extends Character> x) {
    return ((java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0);
  }
  public static boolean IsValid__NonEmptyBlob(dafny.DafnySequence<? extends Byte> x) {
    return (java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0;
  }
  public static boolean IsValid__NonEmptyList(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0;
  }
  public static boolean IsValid__NonEmptyMap(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).size()))) <= 0;
  }
  public static boolean IsValid__NonEmptyString(dafny.DafnySequence<? extends Character> x) {
    return (java.math.BigInteger.ONE).compareTo((java.math.BigInteger.valueOf((x).length()))) <= 0;
  }
  public static boolean IsValid__OneToTen(int x) {
    return ((1) <= (x)) && ((x) <= (10));
  }
  public static boolean IsValid__StringLessThanOrEqualToTen(dafny.DafnySequence<? extends Character> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo((java.math.BigInteger.valueOf(10L))) <= 0;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Constraints.Types_Compile._default";
  }
}
