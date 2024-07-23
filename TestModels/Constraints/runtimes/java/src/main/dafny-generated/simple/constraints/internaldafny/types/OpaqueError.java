// Class OpaqueError
// Dafny class OpaqueError compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class OpaqueError {
  public OpaqueError() {
  }
  public static boolean _Is(Error __source) {
    Error _18_e = __source;
    return (_18_e).is_Opaque();
  }
  private static final dafny.TypeDescriptor<Error> _TYPE = dafny.TypeDescriptor.<Error>referenceWithInitializer(Error.class, () -> Error.Default());
  public static dafny.TypeDescriptor<Error> _typeDescriptor() {
    return (dafny.TypeDescriptor<Error>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
