// Class __default
// Dafny class __default compiled into Java
package WrappedSimpleDependenciesTest_Compile;

import Dafny.Simple.Dependencies.Wrapped.*;
import Helpers_Compile.*;
import SimpleDependenciesImplTest_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void TestDependenciesWithDefaultConfig()
  {
    Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient _64_client;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _65_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _out16;
    _out16 = Dafny.Simple.Dependencies.Wrapped.__default.WrappedSimpleDependencies(Dafny.Simple.Dependencies.Wrapped.__default.WrappedDefaultSimpleDependenciesConfig());
    _65_valueOrError0 = _out16;
    if (!(!((_65_valueOrError0).IsFailure(Dafny.Simple.Dependencies.Types._Companion_ISimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/WrappedSimpleDependenciesTest.dfy(14,19): " + java.lang.String.valueOf(_65_valueOrError0));
    }
    _64_client = (_65_valueOrError0).Extract(Dafny.Simple.Dependencies.Types._Companion_ISimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    SimpleDependenciesImplTest_Compile.__default.TestGetSimpleResource(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseSimpleResource(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseLocalConstraintsService(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseLocalExtendableResource(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysModeledError(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysMultipleErrors(_64_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysOpaqueError(_64_client);
  }
  public static void TestDependenciesWithCustomConfig()
  {
    ExtendableResource_Compile.ExtendableResource _66_extendableResourceReferenceToAssign;
    ExtendableResource_Compile.ExtendableResource _nw1 = new ExtendableResource_Compile.ExtendableResource();
    _nw1.__ctor();
    _66_extendableResourceReferenceToAssign = _nw1;
    Dafny.Simple.Constraints.SimpleConstraintsClient _67_simpleConstraintsServiceReferenceToAssign;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _68_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _out17;
    _out17 = Dafny.Simple.Constraints.__default.SimpleConstraints(Dafny.Simple.Constraints.__default.DefaultSimpleConstraintsConfig());
    _68_valueOrError0 = _out17;
    if (!(!((_68_valueOrError0).IsFailure(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/WrappedSimpleDependenciesTest.dfy(27,54): " + java.lang.String.valueOf(_68_valueOrError0));
    }
    _67_simpleConstraintsServiceReferenceToAssign = (_68_valueOrError0).Extract(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor());
    Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig _69_customConfig;
    _69_customConfig = Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig.create(Wrappers_Compile.Option.<Dafny.Simple.Resources.Types.SimpleResourcesConfig>create_Some(Dafny.Simple.Resources.Types.SimpleResourcesConfig.create(dafny.DafnySequence.asString("default"))), Wrappers_Compile.Option.<Dafny.Simple.Constraints.SimpleConstraintsClient>create_Some(_67_simpleConstraintsServiceReferenceToAssign), Wrappers_Compile.Option.<ExtendableResource_Compile.ExtendableResource>create_Some(_66_extendableResourceReferenceToAssign), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("bw1and10")));
    Dafny.Simple.Dependencies.SimpleDependenciesClient _70_client;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _71_valueOrError1 = (Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _out18;
    _out18 = Dafny.Simple.Dependencies.__default.SimpleDependencies(_69_customConfig);
    _71_valueOrError1 = _out18;
    if (!(!((_71_valueOrError1).IsFailure(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/WrappedSimpleDependenciesTest.dfy(38,19): " + java.lang.String.valueOf(_71_valueOrError1));
    }
    _70_client = (_71_valueOrError1).Extract(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    SimpleDependenciesImplTest_Compile.__default.TestGetSimpleResource(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseSimpleResource(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseLocalConstraintsService(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestUseLocalExtendableResource(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysModeledError(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysMultipleErrors(_70_client);
    SimpleDependenciesImplTest_Compile.__default.TestLocalExtendableResourceAlwaysOpaqueError(_70_client);
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "WrappedSimpleDependenciesTest_Compile._default";
  }
}
