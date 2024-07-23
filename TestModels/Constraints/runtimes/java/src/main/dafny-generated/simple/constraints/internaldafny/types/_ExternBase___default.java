// Class _ExternBase___default
// Dafny class __default compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static boolean IsValid__BlobLessThanOrEqualToTen(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0;
  }
  public static boolean IsValid__GreaterThanOne(int x) {
    return (1) <= (x);
  }
  public static boolean IsValid__LessThanTen(int x) {
    return (x) <= (10);
  }
  public static boolean IsValid__ListLessThanOrEqualToTen(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0;
  }
  public static boolean IsValid__ListOfUtf8Bytes(dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(2L)) <= 0);
  }
  public static boolean IsValid__MapLessThanOrEqualToTen(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.valueOf((x).size())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0;
  }
  public static boolean IsValid__MyBlob(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0);
  }
  public static boolean IsValid__MyList(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0);
  }
  public static boolean IsValid__MyMap(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).size())) <= 0) && ((java.math.BigInteger.valueOf((x).size())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0);
  }
  public static boolean IsValid__MyString(dafny.DafnySequence<? extends Character> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0);
  }
  public static boolean IsValid__NonEmptyBlob(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return (java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0;
  }
  public static boolean IsValid__NonEmptyList(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0;
  }
  public static boolean IsValid__NonEmptyMap(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> x) {
    return (java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).size())) <= 0;
  }
  public static boolean IsValid__NonEmptyString(dafny.DafnySequence<? extends Character> x) {
    return (java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0;
  }
  public static boolean IsValid__OneToTen(int x) {
    return ((1) <= (x)) && ((x) <= (10));
  }
  public static boolean IsValid__StringLessThanOrEqualToTen(dafny.DafnySequence<? extends Character> x) {
    return (java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0;
  }
  public static boolean IsValid__TenToTen(long x) {
    return (((long) -10L) <= (x)) && ((x) <= ((long) 10L));
  }
  public static boolean IsValid__Utf8Bytes(dafny.DafnySequence<? extends java.lang.Byte> x) {
    return ((java.math.BigInteger.ONE).compareTo(java.math.BigInteger.valueOf((x).length())) <= 0) && ((java.math.BigInteger.valueOf((x).length())).compareTo(java.math.BigInteger.valueOf(10L)) <= 0);
  }
  @Override
  public java.lang.String toString() {
    return "SimpleConstraintsTypes._default";
  }
}
