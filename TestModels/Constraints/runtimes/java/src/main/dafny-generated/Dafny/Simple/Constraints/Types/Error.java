// Class Error
// Dafny class Error compiled into Java
package Dafny.Simple.Constraints.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Error {
  public Error() { }

  private static final Error theDefault = Dafny.Simple.Constraints.Types.Error.create_CollectionOfErrors(dafny.DafnySequence.<Error> empty(Error._typeDescriptor()));
  public static Error Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Error> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(Error.class, () -> Default());
  public static dafny.TypeDescriptor<Error> _typeDescriptor() {
    return (dafny.TypeDescriptor<Error>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Error create_CollectionOfErrors(dafny.DafnySequence<? extends Error> list) {
    return new Error_CollectionOfErrors(list);
  }
  public static Error create_Opaque(Object obj) {
    return new Error_Opaque(obj);
  }
  public boolean is_CollectionOfErrors() { return this instanceof Error_CollectionOfErrors; }
  public boolean is_Opaque() { return this instanceof Error_Opaque; }
  public dafny.DafnySequence<? extends Error> dtor_list() {
    Error d = this;
    return ((Error_CollectionOfErrors)d)._list;
  }
  public Object dtor_obj() {
    Error d = this;
    return ((Error_Opaque)d)._obj;
  }
}
