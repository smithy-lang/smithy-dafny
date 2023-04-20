// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny.Simple.Dependencies.Wrapped;


@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig WrappedDefaultSimpleDependenciesConfig() {
    return Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig.create(Wrappers_Compile.Option.<Dafny.Simple.Resources.Types.SimpleResourcesConfig>create_Some(Dafny.Simple.Resources.Types.SimpleResourcesConfig.create(dafny.DafnySequence.asString("default"))), Wrappers_Compile.Option.<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient>create_None(), Wrappers_Compile.Option.<Dafny.Simple.Extendable.Resources.Types.IExtendableResource>create_None(), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("bw1and10")));
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Dependencies.Wrapped_Compile._default";
  }
}
