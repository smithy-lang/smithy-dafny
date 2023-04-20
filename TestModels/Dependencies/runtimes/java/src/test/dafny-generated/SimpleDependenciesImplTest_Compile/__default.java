// Class __default
// Dafny class __default compiled into Java
package SimpleDependenciesImplTest_Compile;

import Dafny.Simple.Dependencies.Wrapped.*;
import Helpers_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static void TestDependenciesWithDefaultConfig()
  {
    Dafny.Simple.Dependencies.SimpleDependenciesClient _34_client;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _35_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _out4;
    _out4 = Dafny.Simple.Dependencies.__default.SimpleDependencies(Dafny.Simple.Dependencies.__default.DefaultSimpleDependenciesConfig());
    _35_valueOrError0 = _out4;
    if (!(!((_35_valueOrError0).IsFailure(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(16,19): " + java.lang.String.valueOf(_35_valueOrError0));
    }
    _34_client = (_35_valueOrError0).Extract(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    __default.TestGetSimpleResource(_34_client);
    __default.TestUseSimpleResource(_34_client);
    __default.TestUseLocalExtendableResource(_34_client);
    __default.TestUseLocalConstraintsService(_34_client);
    __default.TestLocalExtendableResourceAlwaysModeledError(_34_client);
    __default.TestLocalExtendableResourceAlwaysMultipleErrors(_34_client);
    __default.TestLocalExtendableResourceAlwaysOpaqueError(_34_client);
  }
  public static void TestDependenciesWithCustomConfig()
  {
    ExtendableResource_Compile.ExtendableResource _36_extendableResourceReferenceToAssign;
    ExtendableResource_Compile.ExtendableResource _nw0 = new ExtendableResource_Compile.ExtendableResource();
    _nw0.__ctor();
    _36_extendableResourceReferenceToAssign = _nw0;
    Dafny.Simple.Constraints.SimpleConstraintsClient _37_simpleConstraintsServiceReferenceToAssign;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _38_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.SimpleConstraintsClient, Dafny.Simple.Constraints.Types.Error> _out5;
    _out5 = Dafny.Simple.Constraints.__default.SimpleConstraints(Dafny.Simple.Constraints.__default.DefaultSimpleConstraintsConfig());
    _38_valueOrError0 = _out5;
    if (!(!((_38_valueOrError0).IsFailure(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(29,52): " + java.lang.String.valueOf(_38_valueOrError0));
    }
    _37_simpleConstraintsServiceReferenceToAssign = (_38_valueOrError0).Extract(Dafny.Simple.Constraints.SimpleConstraintsClient._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor());
    Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig _39_customConfig;
    _39_customConfig = Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig.create(
      Wrappers_Compile.Option.<Dafny.Simple.Resources.Types.SimpleResourcesConfig>create_Some(Dafny.Simple.Resources.Types.SimpleResourcesConfig.create(dafny.DafnySequence.asString("default"))),
      Wrappers_Compile.Option.<Dafny.Simple.Constraints.SimpleConstraintsClient>create_Some(_37_simpleConstraintsServiceReferenceToAssign),
      Wrappers_Compile.Option.<ExtendableResource_Compile.ExtendableResource>create_Some(_36_extendableResourceReferenceToAssign),
      Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("bw1and10")))
    ;
    Dafny.Simple.Dependencies.SimpleDependenciesClient _40_client;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _41_valueOrError1 = (Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Dependencies.SimpleDependenciesClient, Dafny.Simple.Dependencies.Types.Error> _out6;
    _out6 = Dafny.Simple.Dependencies.__default.SimpleDependencies(_39_customConfig);
    _41_valueOrError1 = _out6;
    if (!(!((_41_valueOrError1).IsFailure(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(40,17): " + java.lang.String.valueOf(_41_valueOrError1));
    }
    _40_client = (_41_valueOrError1).Extract(Dafny.Simple.Dependencies.SimpleDependenciesClient._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    __default.TestGetSimpleResource(_40_client);
    __default.TestUseSimpleResource(_40_client);
    __default.TestUseLocalExtendableResource(_40_client);
    __default.TestUseLocalConstraintsService(_40_client);
    __default.TestLocalExtendableResourceAlwaysModeledError(_40_client);
    __default.TestLocalExtendableResourceAlwaysMultipleErrors(_40_client);
    __default.TestLocalExtendableResourceAlwaysOpaqueError(_40_client);
  }
  public static void TestGetSimpleResource(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Resources.Types.GetResourcesInput _42_input;
    _42_input = Dafny.Simple.Resources.Types.GetResourcesInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("anyInput")));
    Dafny.Simple.Resources.Types.GetResourcesOutput _43_res;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> _44_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> _out7;
    _out7 = (client).GetSimpleResource(_42_input);
    _44_valueOrError0 = _out7;
    if (!(!((_44_valueOrError0).IsFailure(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(58,14): " + java.lang.String.valueOf(_44_valueOrError0));
    }
    _43_res = (_44_valueOrError0).Extract(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
  }
  public static void TestUseSimpleResource(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Resources.Types.GetResourceDataInput _45_resourceDataInput;
    _45_resourceDataInput = Dafny.Simple.Resources.Types.GetResourceDataInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.of((byte) 0, (byte) 1)), Wrappers_Compile.Option.<Boolean>create_Some(true), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("anyString")), Wrappers_Compile.Option.<java.lang.Integer>create_Some(123), Wrappers_Compile.Option.<java.lang.Long>create_Some(123L));
    Dafny.Simple.Resources.Types.GetResourcesInput _46_getResourcesInput;
    _46_getResourcesInput = Dafny.Simple.Resources.Types.GetResourcesInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("anyInput")));
    Dafny.Simple.Resources.Types.GetResourcesOutput _47_getResourcesOutput;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> _48_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> _out8;
    _out8 = (client).GetSimpleResource(_46_getResourcesInput);
    _48_valueOrError0 = _out8;
    if (!(!((_48_valueOrError0).IsFailure(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(77,29): " + java.lang.String.valueOf(_48_valueOrError0));
    }
    _47_getResourcesOutput = (_48_valueOrError0).Extract(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    Dafny.Simple.Dependencies.Types.UseSimpleResourceInput _49_input;
    _49_input = Dafny.Simple.Dependencies.Types.UseSimpleResourceInput.create((_47_getResourcesOutput).dtor_output(), _45_resourceDataInput);
    Dafny.Simple.Resources.Types.GetResourceDataOutput _50_res;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> _51_valueOrError1 = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Resources.Types.GetResourceDataOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> _out9;
    _out9 = (client).UseSimpleResource(_49_input);
    _51_valueOrError1 = _out9;
    if (!(!((_51_valueOrError1).IsFailure(Dafny.Simple.Resources.Types.GetResourceDataOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(84,14): " + java.lang.String.valueOf(_51_valueOrError1));
    }
    _50_res = (_51_valueOrError1).Extract(Dafny.Simple.Resources.Types.GetResourceDataOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
  }
  public static void TestUseLocalConstraintsService(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Constraints.Types.GetConstraintsInput _52_resourceDataInput;
    Dafny.Simple.Constraints.Types.GetConstraintsInput _out10;
    _out10 = Helpers_Compile.__default.GetConstraintsInputTemplate(dafny.DafnySet.<dafny.DafnySequence<? extends Character>> empty());
    _52_resourceDataInput = _out10;
    Dafny.Simple.Constraints.Types.GetConstraintsOutput _53_res;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> _54_valueOrError0 = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> _out11;
    _out11 = (client).UseLocalConstraintsService(_52_resourceDataInput);
    _54_valueOrError0 = _out11;
    if (!(!((_54_valueOrError0).IsFailure(Dafny.Simple.Constraints.Types.GetConstraintsOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(95,14): " + java.lang.String.valueOf(_54_valueOrError0));
    }
    _53_res = (_54_valueOrError0).Extract(Dafny.Simple.Constraints.Types.GetConstraintsOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
    if (!(((_53_res).dtor_MyString()).is_Some())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(96,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!((((_53_res).dtor_MyString()).dtor_value()).equals(dafny.DafnySequence.asString("bw1and10")))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(97,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestUseLocalExtendableResource(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput _55_resourceDataInput;
    _55_resourceDataInput = Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends java.lang.Byte>>create_Some(dafny.DafnySequence.of((byte) 1)), Wrappers_Compile.Option.<Boolean>create_Some(true), Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("Some")), Wrappers_Compile.Option.<java.lang.Integer>create_Some(1), Wrappers_Compile.Option.<java.lang.Long>create_Some(1L));
    Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput _56_res;
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> _57_valueOrError0 = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> _out12;
    _out12 = (client).UseLocalExtendableResource(_55_resourceDataInput);
    _57_valueOrError0 = _out12;
    if (!(!((_57_valueOrError0).IsFailure(Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(115,14): " + java.lang.String.valueOf(_57_valueOrError0));
    }
    _56_res = (_57_valueOrError0).Extract(Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput._typeDescriptor(), Dafny.Simple.Dependencies.Types.Error._typeDescriptor());
  }
  public static void TestLocalExtendableResourceAlwaysModeledError(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput _58_errorInput;
    _58_errorInput = Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("Some")));
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _59_errorOutput;
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out13;
    _out13 = (client).LocalExtendableResourceAlwaysModeledError(_58_errorInput);
    _59_errorOutput = _out13;
    if (!((_59_errorOutput).is_Failure())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(129,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!(((_59_errorOutput).dtor_error()).is_SimpleExtendableResources())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(130,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!((((_59_errorOutput).dtor_error()).dtor_SimpleExtendableResources()).is_SimpleExtendableResourcesException())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(131,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestLocalExtendableResourceAlwaysMultipleErrors(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput _60_errorInput;
    _60_errorInput = Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("Some")));
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _61_errorOutput;
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out14;
    _out14 = (client).LocalExtendableResourceAlwaysMultipleErrors(_60_errorInput);
    _61_errorOutput = _out14;
    if (!((_61_errorOutput).is_Failure())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(145,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!(((_61_errorOutput).dtor_error()).is_SimpleExtendableResources())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(146,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!((((_61_errorOutput).dtor_error()).dtor_SimpleExtendableResources()).is_CollectionOfErrors())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(147,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  public static void TestLocalExtendableResourceAlwaysOpaqueError(Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient client)
  {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput _62_errorInput;
    _62_errorInput = Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput.create(Wrappers_Compile.Option.<dafny.DafnySequence<? extends Character>>create_Some(dafny.DafnySequence.asString("Some")));
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _63_errorOutput;
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out15;
    _out15 = (client).LocalExtendableResourceAlwaysNativeError(_62_errorInput);
    _63_errorOutput = _out15;
    if (!((_63_errorOutput).is_Failure())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(161,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!(((_63_errorOutput).dtor_error()).is_SimpleExtendableResources())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(162,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    if (!((((_63_errorOutput).dtor_error()).dtor_SimpleExtendableResources()).is_Opaque())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/test/SimpleDependenciesImplTest.dfy(163,6): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "SimpleDependenciesImplTest_Compile._default";
  }
}
