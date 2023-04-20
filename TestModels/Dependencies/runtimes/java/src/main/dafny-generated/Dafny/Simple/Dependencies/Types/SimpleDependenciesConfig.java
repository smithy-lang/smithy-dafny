// Class SimpleDependenciesConfig
// Dafny class SimpleDependenciesConfig compiled into Java
package Dafny.Simple.Dependencies.Types;


@SuppressWarnings({"unchecked", "deprecation"})
public class SimpleDependenciesConfig {
  public Wrappers_Compile.Option<Dafny.Simple.Resources.Types.SimpleResourcesConfig> _simpleResourcesConfig;
  public Wrappers_Compile.Option<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient> _simpleConstraintsServiceReference;
  public Wrappers_Compile.Option<Dafny.Simple.Extendable.Resources.Types.IExtendableResource> _extendableResourceReference;
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> _specialString;
  public SimpleDependenciesConfig (Wrappers_Compile.Option<Dafny.Simple.Resources.Types.SimpleResourcesConfig> simpleResourcesConfig, Wrappers_Compile.Option<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient> simpleConstraintsServiceReference, Wrappers_Compile.Option<Dafny.Simple.Extendable.Resources.Types.IExtendableResource> extendableResourceReference, Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> specialString) {
    this._simpleResourcesConfig = simpleResourcesConfig;
    this._simpleConstraintsServiceReference = simpleConstraintsServiceReference;
    this._extendableResourceReference = extendableResourceReference;
    this._specialString = specialString;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) return true;
    if (other == null) return false;
    if (getClass() != other.getClass()) return false;
    SimpleDependenciesConfig o = (SimpleDependenciesConfig)other;
    return true && java.util.Objects.equals(this._simpleResourcesConfig, o._simpleResourcesConfig) && java.util.Objects.equals(this._simpleConstraintsServiceReference, o._simpleConstraintsServiceReference) && java.util.Objects.equals(this._extendableResourceReference, o._extendableResourceReference) && java.util.Objects.equals(this._specialString, o._specialString);
  }
  @Override
  public int hashCode() {
    long hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._simpleResourcesConfig);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._simpleConstraintsServiceReference);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._extendableResourceReference);
    hash = ((hash << 5) + hash) + java.util.Objects.hashCode(this._specialString);
    return (int)hash;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    s.append("Dafny.Simple.Dependencies.Types_Compile.SimpleDependenciesConfig.SimpleDependenciesConfig");
    s.append("(");
    s.append(dafny.Helpers.toString(this._simpleResourcesConfig));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._simpleConstraintsServiceReference));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._extendableResourceReference));
    s.append(", ");
    s.append(dafny.Helpers.toString(this._specialString));
    s.append(")");
    return s.toString();
  }

  private static final SimpleDependenciesConfig theDefault = Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig.create(Wrappers_Compile.Option.<Dafny.Simple.Resources.Types.SimpleResourcesConfig>Default(), Wrappers_Compile.Option.<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient>Default(), Wrappers_Compile.Option.<Dafny.Simple.Extendable.Resources.Types.IExtendableResource>Default(), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>Default());
  public static SimpleDependenciesConfig Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<SimpleDependenciesConfig> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(SimpleDependenciesConfig.class, () -> Default());
  public static dafny.TypeDescriptor<SimpleDependenciesConfig> _typeDescriptor() {
    return (dafny.TypeDescriptor<SimpleDependenciesConfig>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static SimpleDependenciesConfig create(Wrappers_Compile.Option<Dafny.Simple.Resources.Types.SimpleResourcesConfig> simpleResourcesConfig, Wrappers_Compile.Option<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient> simpleConstraintsServiceReference, Wrappers_Compile.Option<Dafny.Simple.Extendable.Resources.Types.IExtendableResource> extendableResourceReference, Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> specialString) {
    return new SimpleDependenciesConfig(simpleResourcesConfig, simpleConstraintsServiceReference, extendableResourceReference, specialString);
  }
  public static SimpleDependenciesConfig create_SimpleDependenciesConfig(Wrappers_Compile.Option<Dafny.Simple.Resources.Types.SimpleResourcesConfig> simpleResourcesConfig, Wrappers_Compile.Option<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient> simpleConstraintsServiceReference, Wrappers_Compile.Option<Dafny.Simple.Extendable.Resources.Types.IExtendableResource> extendableResourceReference, Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> specialString) {
    return create(simpleResourcesConfig, simpleConstraintsServiceReference, extendableResourceReference, specialString);
  }
  public boolean is_SimpleDependenciesConfig() { return true; }
  public Wrappers_Compile.Option<Dafny.Simple.Resources.Types.SimpleResourcesConfig> dtor_simpleResourcesConfig() {
    return this._simpleResourcesConfig;
  }
  public Wrappers_Compile.Option<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient> dtor_simpleConstraintsServiceReference() {
    return this._simpleConstraintsServiceReference;
  }
  public Wrappers_Compile.Option<Dafny.Simple.Extendable.Resources.Types.IExtendableResource> dtor_extendableResourceReference() {
    return this._extendableResourceReference;
  }
  public Wrappers_Compile.Option<dafny.DafnySequence<? extends Character>> dtor_specialString() {
    return this._specialString;
  }
}
