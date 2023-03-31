// Class NonEmptyBlob
// Dafny class NonEmptyBlob compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class NonEmptyBlob {
  public NonEmptyBlob() {
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<Byte> empty(StandardLibrary_mUInt_Compile.uint8._typeDescriptor()));
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends Byte>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends Byte>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
