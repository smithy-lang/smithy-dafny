// Class ListOfUtf8Bytes
// Dafny class ListOfUtf8Bytes compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class ListOfUtf8Bytes {
  public ListOfUtf8Bytes() {
  }
  public static boolean _Is(dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> __source) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>> _4_x = __source;
    return __default.IsValid__ListOfUtf8Bytes(_4_x);
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _TYPE = dafny.TypeDescriptor.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<dafny.DafnySequence<? extends java.lang.Byte>> empty(Utf8Bytes._typeDescriptor()));
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends java.lang.Byte>>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
