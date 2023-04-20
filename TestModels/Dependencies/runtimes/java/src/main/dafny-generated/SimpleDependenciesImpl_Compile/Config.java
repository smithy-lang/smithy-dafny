// Class Config
// Dafny class Config compiled into Java
package SimpleDependenciesImpl_Compile;

import Dafny.Simple.Dependencies.Types.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class Config {
  public Dafny.Simple.Resources.Types.SimpleResourcesConfig _simpleResourcesConfig;
  public Dafny.Simple.Constraints.Types.ISimpleConstraintsClient _simpleConstraintsServiceReference;
  public Dafny.Simple.Extendable.Resources.Types.IExtendableResource _extendableResourceReference;
  public dafny.DafnySequence<? extends Character> _specialString;
  public Config (Dafny.Simple.Resources.Types.SimpleResourcesConfig simpleResourcesConfig, Dafny.Simple.Constraints.Types.ISimpleConstraintsClient simpleConstraintsServiceReference, Dafny.Simple.Extendable.Resources.Types.IExtendableResource extendableResourceReference, dafny.DafnySequence<? extends Character> specialString) {
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
    Config o = (Config)other;
    return true && java.util.Objects.equals(this._simpleResourcesConfig, o._simpleResourcesConfig) && this._simpleConstraintsServiceReference == o._simpleConstraintsServiceReference && this._extendableResourceReference == o._extendableResourceReference && java.util.Objects.equals(this._specialString, o._specialString);
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
    s.append("SimpleDependenciesImpl_Compile.Config.Config");
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

  private static final Config theDefault = SimpleDependenciesImpl_Compile.Config.create(Dafny.Simple.Resources.Types.SimpleResourcesConfig.Default(), null, null, dafny.DafnySequence.<Character> empty(dafny.TypeDescriptor.CHAR));
  public static Config Default() {
    return theDefault;
  }
  private static final dafny.TypeDescriptor<Config> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(Config.class, () -> Default());
  public static dafny.TypeDescriptor<Config> _typeDescriptor() {
    return (dafny.TypeDescriptor<Config>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  public static Config create(Dafny.Simple.Resources.Types.SimpleResourcesConfig simpleResourcesConfig, Dafny.Simple.Constraints.Types.ISimpleConstraintsClient simpleConstraintsServiceReference, Dafny.Simple.Extendable.Resources.Types.IExtendableResource extendableResourceReference, dafny.DafnySequence<? extends Character> specialString) {
    return new Config(simpleResourcesConfig, simpleConstraintsServiceReference, extendableResourceReference, specialString);
  }
  public static Config create_Config(Dafny.Simple.Resources.Types.SimpleResourcesConfig simpleResourcesConfig, Dafny.Simple.Constraints.Types.ISimpleConstraintsClient simpleConstraintsServiceReference, Dafny.Simple.Extendable.Resources.Types.IExtendableResource extendableResourceReference, dafny.DafnySequence<? extends Character> specialString) {
    return create(simpleResourcesConfig, simpleConstraintsServiceReference, extendableResourceReference, specialString);
  }
  public boolean is_Config() { return true; }
  public Dafny.Simple.Resources.Types.SimpleResourcesConfig dtor_simpleResourcesConfig() {
    return this._simpleResourcesConfig;
  }
  public Dafny.Simple.Constraints.Types.ISimpleConstraintsClient dtor_simpleConstraintsServiceReference() {
    return this._simpleConstraintsServiceReference;
  }
  public Dafny.Simple.Extendable.Resources.Types.IExtendableResource dtor_extendableResourceReference() {
    return this._extendableResourceReference;
  }
  public dafny.DafnySequence<? extends Character> dtor_specialString() {
    return this._specialString;
  }
}
