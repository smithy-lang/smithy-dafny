// Class Error
// Dafny class Error compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class Error {
  public Error() { }

  private static final Error theDefault = Dafny.Simple.Dependencies.Types.Error.create_SimpleConstraints(Dafny.Simple.Constraints.Types.Error.Default());
  public static Error Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Error> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(Error.class, () -> Default());
  public static dafny.TypeDescriptor<Error> _typeDescriptor() {
    return (dafny.TypeDescriptor<Error>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Error create_SimpleConstraints(Dafny.Simple.Constraints.Types.Error SimpleConstraints) {
    return new Error_SimpleConstraints(SimpleConstraints);
  }
  public static Error create_SimpleExtendableResources(Dafny.Simple.Extendable.Resources.Types.Error SimpleExtendableResources) {
    return new Error_SimpleExtendableResources(SimpleExtendableResources);
  }
  public static Error create_SimpleResources(Dafny.Simple.Resources.Types.Error SimpleResources) {
    return new Error_SimpleResources(SimpleResources);
  }
  public static Error create_CollectionOfErrors(dafny.DafnySequence<? extends Error> list) {
    return new Error_CollectionOfErrors(list);
  }
  public static Error create_Opaque(Object obj) {
    return new Error_Opaque(obj);
  }
  public boolean is_SimpleConstraints() { return this instanceof Error_SimpleConstraints; }
  public boolean is_SimpleExtendableResources() { return this instanceof Error_SimpleExtendableResources; }
  public boolean is_SimpleResources() { return this instanceof Error_SimpleResources; }
  public boolean is_CollectionOfErrors() { return this instanceof Error_CollectionOfErrors; }
  public boolean is_Opaque() { return this instanceof Error_Opaque; }
  public Dafny.Simple.Constraints.Types.Error dtor_SimpleConstraints() {
    Error d = this;
    return ((Error_SimpleConstraints)d)._SimpleConstraints;
  }
  public Dafny.Simple.Extendable.Resources.Types.Error dtor_SimpleExtendableResources() {
    Error d = this;
    return ((Error_SimpleExtendableResources)d)._SimpleExtendableResources;
  }
  public Dafny.Simple.Resources.Types.Error dtor_SimpleResources() {
    Error d = this;
    return ((Error_SimpleResources)d)._SimpleResources;
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
