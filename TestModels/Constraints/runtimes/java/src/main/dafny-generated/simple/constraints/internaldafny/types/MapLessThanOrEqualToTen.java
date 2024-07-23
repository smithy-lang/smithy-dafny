// Class MapLessThanOrEqualToTen
// Dafny class MapLessThanOrEqualToTen compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class MapLessThanOrEqualToTen {
  public MapLessThanOrEqualToTen() {
  }
  public static boolean _Is(dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> __source) {
    dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>> _5_x = __source;
    return __default.IsValid__MapLessThanOrEqualToTen(_5_x);
  }
  private static final dafny.TypeDescriptor<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _TYPE = dafny.TypeDescriptor.<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>referenceWithInitializer(dafny.DafnyMap.class, () -> dafny.DafnyMap.<dafny.DafnySequence<? extends Character>,dafny.DafnySequence<? extends Character>> empty());
  public static dafny.TypeDescriptor<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>> _typeDescriptor() {
    return (dafny.TypeDescriptor<dafny.DafnyMap<? extends dafny.DafnySequence<? extends Character>, ? extends dafny.DafnySequence<? extends Character>>>) (dafny.TypeDescriptor<?>) _TYPE;
  }
}
