// Class NonEmptyList
// Dafny class NonEmptyList compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class NonEmptyList {
  public NonEmptyList() {
  }
  public static boolean _Is(dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> __source) {
    dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>> _11_x = __source;
    return __default.IsValid__NonEmptyList(_11_x);
  }
  private static final dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _TYPE = dafny.TypeDescriptor.<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>referenceWithInitializer(dafny.DafnySequence.class, () -> dafny.DafnySequence.<dafny.DafnySequence<? extends Character>> empty(MyString._typeDescriptor()));
  public static dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnySequence<? extends dafny.DafnySequence<? extends Character>>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
