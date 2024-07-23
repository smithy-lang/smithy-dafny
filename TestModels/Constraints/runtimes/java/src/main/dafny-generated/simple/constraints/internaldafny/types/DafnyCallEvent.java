// Class DafnyCallEvent<I, O>
// Dafny class DafnyCallEvent<I, O> compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public class DafnyCallEvent<I, O> {
  public I _input;
  public O _output;
  protected dafny.TypeDescriptor<I> _td_I;
  protected dafny.TypeDescriptor<O> _td_O;
  public DafnyCallEvent (dafny.TypeDescriptor<I> _td_I, dafny.TypeDescriptor<O> _td_O, I input, O output) {
    this._td_I = _td_I;
    this._td_O = _td_O;
    this._input = input;
    this._output = output;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    DafnyCallEvent<I, O> o = (DafnyCallEvent<I, O>)other;
    return true && java.util.Objects.equals(this._input, o._input) && java.util.Objects.equals(this._output, o._output);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._input);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._output);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("SimpleConstraintsTypes.DafnyCallEvent.DafnyCallEvent");
    s.append("(");
    s.append(dafny.Helpers.toString(this._input));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._output));
    s.append(")");
    return s.toString();
  }
  public static <I, O> dafny.TypeDescriptor<DafnyCallEvent<I, O>> _typeDescriptor(dafny.TypeDescriptor<I> _td_I, dafny.TypeDescriptor<O> _td_O) {
    return (dafny.TypeDescriptor<DafnyCallEvent<I, O>>) (dafny.TypeDescriptor<?>) dafny.TypeDescriptor.<DafnyCallEvent<I, O>>referenceWithInitializer(DafnyCallEvent.class, () -> DafnyCallEvent.<I, O>Default(_td_I, _td_O, _td_I.defaultValue(), _td_O.defaultValue()));
  }

  public static <I, O> DafnyCallEvent<I, O> Default(dafny.TypeDescriptor<I> _td_I, dafny.TypeDescriptor<O> _td_O, I _default_I, O _default_O) {
    return simple.constraints.internaldafny.types.DafnyCallEvent.<I, O>create(_td_I, _td_O, _default_I, _default_O);
  }
  public static <I, O> DafnyCallEvent<I, O> create(dafny.TypeDescriptor<I> _td_I, dafny.TypeDescriptor<O> _td_O, I input, O output) {
    return new DafnyCallEvent<I, O>(_td_I, _td_O, input, output);
  }
  public static <I, O> DafnyCallEvent<I, O> create_DafnyCallEvent(dafny.TypeDescriptor<I> _td_I, dafny.TypeDescriptor<O> _td_O, I input, O output) {
    return create(_td_I, _td_O, input, output);
  }
  public boolean is_DafnyCallEvent() { return true; }
  public I dtor_input() {
    return this._input;
  }
  public O dtor_output() {
    return this._output;
  }
}
