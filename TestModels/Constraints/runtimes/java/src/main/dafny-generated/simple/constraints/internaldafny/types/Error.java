// Class Error
// Dafny class Error compiled into Java
package simple.constraints.internaldafny.types;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Error {
  public Error() {
  }
  private static final dafny.TypeDescriptor<Error> _TYPE = dafny.TypeDescriptor.<Error>referenceWithInitializer(Error.class, () -> Error.Default());
  public static dafny.TypeDescriptor<Error> _typeDescriptor() {
    return (dafny.TypeDescriptor<Error>) (dafny.TypeDescriptor<?>) _TYPE;
  }

  private static final Error theDefault = simple.constraints.internaldafny.types.Error.create_SimpleConstraintsException(dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR));
  public static Error Default() {
    return theDefault;
  }
  public static Error create_SimpleConstraintsException(dafny.DafnySequence<? extends Character> message) {
    return new Error_SimpleConstraintsException(message);
  }
  public static Error create_CollectionOfErrors(dafny.DafnySequence<? extends Error> list, dafny.DafnySequence<? extends Character> message) {
    return new Error_CollectionOfErrors(list, message);
  }
  public static Error create_Opaque(Object obj) {
    return new Error_Opaque(obj);
  }
  public boolean is_SimpleConstraintsException() { return this instanceof Error_SimpleConstraintsException; }
  public boolean is_CollectionOfErrors() { return this instanceof Error_CollectionOfErrors; }
  public boolean is_Opaque() { return this instanceof Error_Opaque; }
  public dafny.DafnySequence<? extends Character> dtor_message() {
    Error d = this;
    if (d instanceof Error_SimpleConstraintsException) { return ((Error_SimpleConstraintsException)d)._message; }
    return ((Error_CollectionOfErrors)d)._message;
  }
  public dafny.DafnySequence<? extends Error> dtor_list() {
    Error d = this;
    return ((Error_CollectionOfErrors)d)._list;
  }
  public Object dtor_obj() {
    Error d = this;
    return ((Error_Opaque)d)._obj;
  }
}
