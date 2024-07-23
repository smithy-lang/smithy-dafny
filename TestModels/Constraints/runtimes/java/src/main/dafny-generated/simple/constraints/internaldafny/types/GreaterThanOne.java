// Class GreaterThanOne
// Dafny class GreaterThanOne compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class GreaterThanOne {
  public GreaterThanOne() {
  }
  public static boolean _Is(int __source) {
    int _1_x = (__source);
    if (true) {
      return __default.IsValid__GreaterThanOne(_1_x);
    }
    return false;
  }
  private static final dafny.TypeDescriptor<java.lang.Integer> _TYPE = dafny.TypeDescriptor.intWithDefault(0);
  public static dafny.TypeDescriptor<java.lang.Integer> _typeDescriptor() {
    return (dafny.TypeDescriptor<java.lang.Integer>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
