// Class StringLessThanOrEqualToTen
// Dafny class StringLessThanOrEqualToTen compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class StringLessThanOrEqualToTen {
  public StringLessThanOrEqualToTen() {
  }
  public static boolean _Is(dafny.DafnySequence<? extends Character> __source) {
    dafny.DafnySequence<? extends Character> _15_x = __source;
    return __default.IsValid__StringLessThanOrEqualToTen(_15_x);
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence<? extends Character>> _TYPE = dafny.TypeDescriptor.<dafny.DafnySequence<? extends Character>>referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR));
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends Character>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends Character>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
