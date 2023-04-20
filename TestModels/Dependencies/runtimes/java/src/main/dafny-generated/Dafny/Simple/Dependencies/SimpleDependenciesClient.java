// Class SimpleDependenciesClient
// Dafny class SimpleDependenciesClient compiled into Java
package Dafny.Simple.Dependencies;

import Dafny.Simple.Dependencies.Types.*;
import SimpleDependenciesImpl_Compile.*;

@SuppressWarnings({"unchecked", "deprecation"})
public class SimpleDependenciesClient implements Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient {
  public SimpleDependenciesClient() {
    this._config = (SimpleDependenciesImpl_Compile.Config)null;
  }
  public void __ctor(SimpleDependenciesImpl_Compile.Config config)
  {
    (this)._config = config;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> GetSimpleResource(Dafny.Simple.Resources.Types.GetResourcesInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> output = (Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error>)null;
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Dafny.Simple.Dependencies.Types.Error> _out5;
      _out5 = SimpleDependenciesImpl_Compile.__default.GetSimpleResource((this).config(), input);
      output = _out5;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> UseSimpleResource(Dafny.Simple.Dependencies.Types.UseSimpleResourceInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Resources.Types.GetResourceDataOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Dafny.Simple.Dependencies.Types.Error> _out6;
      _out6 = SimpleDependenciesImpl_Compile.__default.UseSimpleResource((this).config(), input);
      output = _out6;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> UseLocalConstraintsService(Dafny.Simple.Constraints.Types.GetConstraintsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Constraints.Types.GetConstraintsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Dafny.Simple.Dependencies.Types.Error> _out7;
      _out7 = SimpleDependenciesImpl_Compile.__default.UseLocalConstraintsService((this).config(), input);
      output = _out7;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> UseLocalExtendableResource(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Dafny.Simple.Dependencies.Types.Error> _out8;
      _out8 = SimpleDependenciesImpl_Compile.__default.UseLocalExtendableResource((this).config(), input);
      output = _out8;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysModeledError(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out9;
      _out9 = SimpleDependenciesImpl_Compile.__default.LocalExtendableResourceAlwaysModeledError((this).config(), input);
      output = _out9;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysMultipleErrors(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out10;
      _out10 = SimpleDependenciesImpl_Compile.__default.LocalExtendableResourceAlwaysMultipleErrors((this).config(), input);
      output = _out10;
    }
    return output;
  }
  public Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> LocalExtendableResourceAlwaysNativeError(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput input)
  {
    Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> output = Wrappers_Compile.Result.<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error>Default(Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput.Default());
    if(true) {
      Wrappers_Compile.Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Dafny.Simple.Dependencies.Types.Error> _out11;
      _out11 = SimpleDependenciesImpl_Compile.__default.LocalExtendableResourceAlwaysNativeError((this).config(), input);
      output = _out11;
    }
    return output;
  }
  public SimpleDependenciesImpl_Compile.Config _config;
  public SimpleDependenciesImpl_Compile.Config config()
  {
    return this._config;
  }
  private static final dafny.TypeDescriptor<SimpleDependenciesClient> _TYPE = dafny.TypeDescriptor.referenceWithInitializer(SimpleDependenciesClient.class, () -> (SimpleDependenciesClient) null);
  public static dafny.TypeDescriptor<SimpleDependenciesClient> _typeDescriptor() {
    return (dafny.TypeDescriptor<SimpleDependenciesClient>) (dafny.TypeDescriptor<?>) _TYPE;
  }
  @Override
  public java.lang.String toString() {
    return "Dafny.Simple.Dependencies_Compile.SimpleDependenciesClient";
  }
}
