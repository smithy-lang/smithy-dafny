// Class BlobLessThanOrEqualToTen
// Dafny class BlobLessThanOrEqualToTen compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class BlobLessThanOrEqualToTen {
  public BlobLessThanOrEqualToTen() {
  }
  public static boolean _Is(dafny.DafnySequence<? extends java.lang.Byte> __source) {
    dafny.DafnySequence<? extends java.lang.Byte> _0_x = __source;
    return __default.IsValid__BlobLessThanOrEqualToTen(_0_x);
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Byte>> _TYPE = dafny.TypeDescriptor.<dafny.DafnySequence<? extends java.lang.Byte>>referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<java.lang.Byte> empty(StandardLibrary_Compile.UInt_Compile.uint8._typeDescriptor()));
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Byte>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends java.lang.Byte>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
