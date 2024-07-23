// Class TenToTen
// Dafny class TenToTen compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class TenToTen {
  public TenToTen() {
  }
  public static boolean _Is(long __source) {
    long _16_x = (__source);
    if (true) {
      return __default.IsValid__TenToTen(_16_x);
    }
    return false;
  }
  private static final dafny.TypeDescriptor<java.lang.Long> _TYPE = dafny.TypeDescriptor.longWithDefault(0L);
  public static dafny.TypeDescriptor<java.lang.Long> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.lang.Long>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
