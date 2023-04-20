// Class UseSimpleResourceInput
// Dafny class UseSimpleResourceInput compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class UseSimpleResourceInput {
  public Dafny.Simple.Resources.Types.ISimpleResource _value;
  public Dafny.Simple.Resources.Types.GetResourceDataInput _input;
  public UseSimpleResourceInput (Dafny.Simple.Resources.Types.ISimpleResource value, Dafny.Simple.Resources.Types.GetResourceDataInput input) {
    this._value = value;
    this._input = input;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    UseSimpleResourceInput o = (UseSimpleResourceInput)other;
    return true && this._value == o._value && java.util.Objects.equals(this._input, o._input);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._value);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._input);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Dependencies.Types_Compile.UseSimpleResourceInput.UseSimpleResourceInput");
    s.append("(");
    s.append(dafny.Helpers.toString(this._value));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._input));
    s.append(")");
    return s.toString();
  }

  private static final UseSimpleResourceInput theDefault = Dafny.Simple.Dependencies.Types.UseSimpleResourceInput.create(null, Dafny.Simple.Resources.Types.GetResourceDataInput.Default());
  public static UseSimpleResourceInput Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<UseSimpleResourceInput> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(UseSimpleResourceInput.class, () -> Default());
  public static dafny.TypeDescriptor<UseSimpleResourceInput> _typeDescriptor() {
    return (dafny.TypeDescriptor<UseSimpleResourceInput>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static UseSimpleResourceInput create(Dafny.Simple.Resources.Types.ISimpleResource value, Dafny.Simple.Resources.Types.GetResourceDataInput input) {
    return new UseSimpleResourceInput(value, input);
  }
  public static UseSimpleResourceInput create_UseSimpleResourceInput(Dafny.Simple.Resources.Types.ISimpleResource value, Dafny.Simple.Resources.Types.GetResourceDataInput input) {
    return create(value, input);
  }
  public boolean is_UseSimpleResourceInput() { return true; }
  public Dafny.Simple.Resources.Types.ISimpleResource dtor_value() {
    return this._value;
  }
  public Dafny.Simple.Resources.Types.GetResourceDataInput dtor_input() {
    return this._input;
  }
}
