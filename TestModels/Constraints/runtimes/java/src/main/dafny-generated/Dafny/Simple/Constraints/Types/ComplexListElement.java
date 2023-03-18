// Class ComplexListElement
// Dafny class ComplexListElement compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class ComplexListElement {
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _value;
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Byte>> _blob;
  public ComplexListElement (Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> value, Wrappers_Compile.Option<dafny.DafnySequence<? extends Byte>> blob) {
    this._value = value;
    this._blob = blob;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    ComplexListElement o = (ComplexListElement)other;
    return true && java.util.Objects.equals(this._value, o._value) && java.util.Objects.equals(this._blob, o._blob);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._value);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._blob);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Constraints.Types_Compile.ComplexListElement.ComplexListElement");
    s.append("(");
    s.append(dafny.Helpers.toString(this._value));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._blob));
    s.append(")");
    return s.toString();
  }

  private static final ComplexListElement theDefault = Dafny.Simple.Constraints.Types.ComplexListElement.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>Default(), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Byte>>Default());
  public static ComplexListElement Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<ComplexListElement> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(ComplexListElement.class, () -> Default());
  public static dafny.TypeDescriptor<ComplexListElement> _typeDescriptor() {
    return (dafny.TypeDescriptor<ComplexListElement>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static ComplexListElement create(Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> value, Wrappers_Compile.Option<dafny.DafnySequence<? extends Byte>> blob) {
    return new ComplexListElement(value, blob);
  }
  public boolean is_ComplexListElement() { return true; }
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> dtor_value() {
    return this._value;
  }
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Byte>> dtor_blob() {
    return this._blob;
  }
}
