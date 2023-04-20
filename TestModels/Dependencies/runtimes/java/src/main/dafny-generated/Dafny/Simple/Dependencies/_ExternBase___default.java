// Class _ExternBase___default
// Dafny class __default compiled into Java
package Dafny.Simple.Dependencies;

import Dafny.Simple.Dependencies.Types.*;
import SimpleDependenciesImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public abstract class _ExternBase___default {
  public _ExternBase___default() {
  }
  public static Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig DefaultSimpleDependenciesConfig() {
    return Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig.create(Wrappers_Compile.Option.<Dafny.Simple.Resources.Types.SimpleResourcesConfig>create_Some(Dafny.Simple.Resources.Types.SimpleResourcesConfig.create(dafny.DafnySequence.asString("default"))), Wrappers_Compile.Option.<Dafny.Simple.Constraints.Types.ISimpleConstraintsClient>create_None(), Wrappers_Compile.Option.<Dafny.Simple.Extendable.Resources.Types.IExtendableResource>create_None(), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("bw1and10")));
  }
  public static Wrappers_Compile.Result<SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> SimpleDependencies(Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig config)
  {
    Wrappers_Compile.Result<SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> res = (Wrappers_Compile.Result<SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>)null;
    if (!(((config).dtor_simpleResourcesConfig()).is_Some())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/Index.dfy(28,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!(((config).dtor_specialString()).is_Some())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/Index.dfy(29,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    Dafny.Simple.Extendable.Resources.Types.IExtendableResource _26_extendableResourceReferenceToAssign = null;
    if (((config).dtor_extendableResourceReference()).is_Some()) {
      _26_extendableResourceReferenceToAssign = ((config).dtor_extendableResourceReference()).dtor_value();
    } else {
      ExtendableResource_Compile.ExtendableResource _nw1 = new ExtendableResource_Compile.ExtendableResource();
      _nw1.__ctor();
      _26_extendableResourceReferenceToAssign = _nw1;
    }
    Dafny.Simple.Constraints.Types.ISimpleConstraintsClient _27_simpleConstraintsServiceReferenceToAssign = null;
    if (((config).dtor_simpleConstraintsServiceReference()).is_Some()) {
      _27_simpleConstraintsServiceReferenceToAssign = ((config).dtor_simpleConstraintsServiceReference()).dtor_value();
    } else {
      Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _28_newSimpleConstraintsServiceReference;
      Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _out12;
      _out12 = Dafny.Simple.Constraints.__default.SimpleConstraints(Dafny.Simple.Constraints.__default.DefaultSimpleConstraintsConfig());
      _28_newSimpleConstraintsServiceReference = _out12;
      if (!((_28_newSimpleConstraintsServiceReference).is_Success())) {
        throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/Index.dfy(47,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
      }
      _27_simpleConstraintsServiceReferenceToAssign = (_28_newSimpleConstraintsServiceReference).dtor_value();
    }
    SimpleDependenciesImpl_Compile.Config _29_configToAssign;
    _29_configToAssign = SimpleDependenciesImpl_Compile.Config.create(((config).dtor_simpleResourcesConfig()).dtor_value(), _27_simpleConstraintsServiceReferenceToAssign, _26_extendableResourceReferenceToAssign, ((config).dtor_specialString()).dtor_value());
    SimpleDependenciesClient _30_client;
    SimpleDependenciesClient _nw2 = new SimpleDependenciesClient();
    _nw2.__ctor(_29_configToAssign);
    _30_client = _nw2;
    res = Wrappers_Compile.Result.<SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>create_Success(_30_client);
    return res;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Dependencies_Compile._default";
  }
}
