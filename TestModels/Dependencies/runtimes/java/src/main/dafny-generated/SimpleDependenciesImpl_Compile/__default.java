// Class __default
// Dafny class __default compiled into Java
package SimpleDependenciesImpl_Compile;

import Dafny.Simple.Dependencies.Types.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class __default {
  public __default() {
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> GetSimpleResource(Config config, Dafny.Simple.Resources.Types.GetResourcesInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> output = (Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error>)null;
    if (!(((input).dtor_value()).is_Some())) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(82,4): " + (dafny.DafnySequence.asString("expectation violation")).verbatimString());
    }
    Dafny.Simple.Resources.Types.SimpleResourcesConfig _0_simpleResourcesConfig;
    _0_simpleResourcesConfig = (config).dtor_simpleResourcesConfig();
    Dafny.Simple.Resources.SimpleResourcesClient _1_client;
    Wrappers_Compile.Result<Dafny.Simple.Resources.SimpleResourcesClient, Dafny.Simple.Resources.Types.Error> _2_valueOrError0 = (Wrappers_Compile.Result<Dafny.Simple.Resources.SimpleResourcesClient, Dafny.Simple.Resources.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Resources.SimpleResourcesClient, Dafny.Simple.Resources.Types.Error> _out0;
    _out0 = Dafny.Simple.Resources.__default.SimpleResources(_0_simpleResourcesConfig);
    _2_valueOrError0 = _out0;
    if (!(!((_2_valueOrError0).IsFailure(Dafny.Simple.Resources.SimpleResourcesClient._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(86,54): " + java.lang.String.valueOf(_2_valueOrError0));
    }
    _1_client = (_2_valueOrError0).Extract(Dafny.Simple.Resources.SimpleResourcesClient._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor());
    Dafny.Simple.Resources.Types.GetResourcesOutput _3_res;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Resources.Types.Error> _4_valueOrError1 = (Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Resources.Types.Error>)null;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Resources.Types.Error> _out1;
    _out1 = (_1_client).GetResources(input);
    _4_valueOrError1 = _out1;
    if (!(!((_4_valueOrError1).IsFailure(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(90,12): " + java.lang.String.valueOf(_4_valueOrError1));
    }
    _3_res = (_4_valueOrError1).Extract(Dafny.Simple.Resources.Types.GetResourcesOutput._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor());
    output = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error>create_Success(_3_res);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> UseSimpleResource(Config config, Dafny.Simple.Dependencies.Types.UseSimpleResourceInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Resources.Types.GetResourceDataOutput.Default());
    Dafny.Simple.Resources.Types.ISimpleResource _5_reference;
    _5_reference = (input).dtor_value();
    Dafny.Simple.Resources.Types.GetResourceDataInput _6_getResourceDataInput;
    _6_getResourceDataInput = (input).dtor_input();
    Dafny.Simple.Resources.Types.GetResourceDataOutput _7_res;
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Resources.Types.Error> _8_valueOrError0 = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Resources.Types.Error>Default(Dafny.Simple.Resources.Types.GetResourceDataOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Resources.Types.Error> _out2;
    _out2 = (_5_reference).GetResourceData(_6_getResourceDataInput);
    _8_valueOrError0 = _out2;
    if (!(!((_8_valueOrError0).IsFailure(Dafny.Simple.Resources.Types.GetResourceDataOutput._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(100,56): " + java.lang.String.valueOf(_8_valueOrError0));
    }
    _7_res = (_8_valueOrError0).Extract(Dafny.Simple.Resources.Types.GetResourceDataOutput._typeDescriptor(), Dafny.Simple.Resources.Types.Error._typeDescriptor());
    output = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error>create_Success(_7_res);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> UseLocalConstraintsService(Config config, Dafny.Simple.Constraints.Types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    Dafny.Simple.Constraints.Types.ISimpleConstraintsClient _9_simpleConstraintsService;
    _9_simpleConstraintsService = (config).dtor_simpleConstraintsServiceReference();
    Dafny.Simple.Constraints.Types.GetConstraintsOutput _10_res;
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> _11_valueOrError0 = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Constraints.Types.Error> _out3;
    _out3 = (_9_simpleConstraintsService).GetConstraints(input);
    _11_valueOrError0 = _out3;
    if (!(!((_11_valueOrError0).IsFailure(Dafny.Simple.Constraints.Types.GetConstraintsOutput._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(108,12): " + java.lang.String.valueOf(_11_valueOrError0));
    }
    _10_res = (_11_valueOrError0).Extract(Dafny.Simple.Constraints.Types.GetConstraintsOutput._typeDescriptor(), Dafny.Simple.Constraints.Types.Error._typeDescriptor());
    output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error>create_Success(_10_res);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> UseLocalExtendableResource(Config config, Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput.Default());
    Dafny.Simple.Extendable.Resources.Types.IExtendableResource _12_reference;
    _12_reference = (config).dtor_extendableResourceReference();
    Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceInput _13_callInput;
    _13_callInput = Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceInput.create(_12_reference, input);
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput _14_res;
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput, Dafny.Simple.Extendable.Resources.Types.Error> _15_valueOrError0 = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput, Dafny.Simple.Extendable.Resources.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput.Default());
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput, Dafny.Simple.Extendable.Resources.Types.Error> _out4;
    _out4 = (_12_reference).GetExtendableResourceData(input);
    _15_valueOrError0 = _out4;
    if (!(!((_15_valueOrError0).IsFailure(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput._typeDescriptor(), Dafny.Simple.Extendable.Resources.Types.Error._typeDescriptor())))) {
      throw new dafny.DafnyHaltException("/Volumes/workplace/ryan-new-world/smithy-dafny/TestModels/Dependencies/src/SimpleDependenciesImpl.dfy(121,12): " + java.lang.String.valueOf(_15_valueOrError0));
    }
    _14_res = (_15_valueOrError0).Extract(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataOutput._typeDescriptor(), Dafny.Simple.Extendable.Resources.Types.Error._typeDescriptor());
    Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput _16_toReturn;
    _16_toReturn = Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput.create(_14_res);
    output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error>create_Success(_16_toReturn);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysModeledError(Config config, Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    Dafny.Simple.Extendable.Resources.Types.Error _17_extendableResourceError;
    _17_extendableResourceError = Dafny.Simple.Extendable.Resources.Types.Error.create_SimpleExtendableResourcesException(dafny.DafnySequence.asString("Hard Coded Exception in src/dafny"));
    Dafny.Simple.Dependencies.Types.Error _18_dependenciesError;
    _18_dependenciesError = Dafny.Simple.Dependencies.Types.Error.create_SimpleExtendableResources(_17_extendableResourceError);
    output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>create_Failure(_18_dependenciesError);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysMultipleErrors(Config config, Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    Dafny.Simple.Extendable.Resources.Types.Error _19_nestedExtendableResourceError;
    _19_nestedExtendableResourceError = Dafny.Simple.Extendable.Resources.Types.Error.create_SimpleExtendableResourcesException(dafny.DafnySequence.asString("Hard Coded Modeled Exception in Collection"));
    Dafny.Simple.Extendable.Resources.Types.Error _20_nestedExtendableResourceError2;
    _20_nestedExtendableResourceError2 = Dafny.Simple.Extendable.Resources.Types.Error.create_SimpleExtendableResourcesException(dafny.DafnySequence.asString("msg no 2"));
    Dafny.Simple.Extendable.Resources.Types.Error _21_collectionOfExtendableResourceErrors;
    _21_collectionOfExtendableResourceErrors = Dafny.Simple.Extendable.Resources.Types.Error.create_CollectionOfErrors(dafny.DafnySequence.of(Dafny.Simple.Extendable.Resources.Types.Error._typeDescriptor(), _19_nestedExtendableResourceError, _20_nestedExtendableResourceError2));
    Dafny.Simple.Dependencies.Types.Error _22_dependenciesError;
    _22_dependenciesError = Dafny.Simple.Dependencies.Types.Error.create_SimpleExtendableResources(_21_collectionOfExtendableResourceErrors);
    output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>create_Failure(_22_dependenciesError);
    return output;
  }
  public static Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysNativeError(Config config, Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    Object _23_obj;
    ExtendableResource_Compile.OpaqueMessage _nw0 = new ExtendableResource_Compile.OpaqueMessage();
    _nw0.__ctor();
    _23_obj = _nw0;
    Dafny.Simple.Extendable.Resources.Types.Error _24_extendableResourceError;
    _24_extendableResourceError = Dafny.Simple.Extendable.Resources.Types.Error.create_Opaque(_23_obj);
    Dafny.Simple.Dependencies.Types.Error _25_dependenciesError;
    _25_dependenciesError = Dafny.Simple.Dependencies.Types.Error.create_SimpleExtendableResources(_24_extendableResourceError);
    output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>create_Failure(_25_dependenciesError);
    return output;
  }
  private static final dafny.TypeDescriptor<__default> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(__default.class, () -> (__default) null);
  public static dafny.TypeDescriptor<__default> _typeDescriptor() {
    return (dafny.TypeDescriptor<__default>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "SimpleDependenciesImpl_Compile._default";
  }
}
