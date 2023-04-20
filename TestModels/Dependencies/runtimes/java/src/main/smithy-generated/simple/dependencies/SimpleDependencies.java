// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies;

import Dafny.Simple.Dependencies.SimpleDependenciesClient;
import Dafny.Simple.Dependencies.Types.Error;
import Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient;
import Dafny.Simple.Dependencies.__default;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import simple.constraints.model.GetConstraintsInput;
import simple.constraints.model.GetConstraintsOutput;
import simple.dependencies.model.SimpleDependenciesConfig;
import simple.dependencies.model.UseSimpleResourceInput;
import simple.extendable.resources.model.GetExtendableResourceDataInput;
import simple.extendable.resources.model.GetExtendableResourceErrorsInput;
import simple.extendable.resources.model.GetExtendableResourceErrorsOutput;
import simple.extendable.resources.model.UseExtendableResourceOutput;
import simple.resources.model.GetResourceDataOutput;
import simple.resources.model.GetResourcesInput;
import simple.resources.model.GetResourcesOutput;

public class SimpleDependencies {
  private final ISimpleDependenciesClient _impl;

  protected SimpleDependencies(BuilderImpl builder) {
    SimpleDependenciesConfig nativeValue = builder.SimpleDependenciesConfig();
    Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig dafnyValue = ToDafny.SimpleDependenciesConfig(nativeValue);
    Result<SimpleDependenciesClient, Error> result = __default.SimpleDependencies(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  SimpleDependencies(ISimpleDependenciesClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public GetResourcesOutput GetSimpleResource(GetResourcesInput nativeValue) {
    Dafny.Simple.Resources.Types.GetResourcesInput dafnyValue = simple.resources.ToDafny.GetResourcesInput(nativeValue);
    Result<Dafny.Simple.Resources.Types.GetResourcesOutput, Error> result = this._impl.GetSimpleResource(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.resources.ToNative.GetResourcesOutput(result.dtor_value());
  }

  public GetResourceDataOutput UseSimpleResource(UseSimpleResourceInput nativeValue) {
    Dafny.Simple.Dependencies.Types.UseSimpleResourceInput dafnyValue = ToDafny.UseSimpleResourceInput(nativeValue);
    Result<Dafny.Simple.Resources.Types.GetResourceDataOutput, Error> result = this._impl.UseSimpleResource(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.resources.ToNative.GetResourceDataOutput(result.dtor_value());
  }

  public GetConstraintsOutput UseLocalConstraintsService(GetConstraintsInput nativeValue) {
    Dafny.Simple.Constraints.Types.GetConstraintsInput dafnyValue = simple.constraints.ToDafny.GetConstraintsInput(nativeValue);
    Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Error> result = this._impl.UseLocalConstraintsService(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.constraints.ToNative.GetConstraintsOutput(result.dtor_value());
  }

  public UseExtendableResourceOutput UseLocalExtendableResource(
      GetExtendableResourceDataInput nativeValue) {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput dafnyValue = simple.extendable.resources.ToDafny.GetExtendableResourceDataInput(nativeValue);
    Result<Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput, Error> result = this._impl.UseLocalExtendableResource(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.extendable.resources.ToNative.UseExtendableResourceOutput(result.dtor_value());
  }

  public GetExtendableResourceErrorsOutput LocalExtendableResourceAlwaysModeledError(
      GetExtendableResourceErrorsInput nativeValue) {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput dafnyValue = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsInput(nativeValue);
    Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> result = this._impl.LocalExtendableResourceAlwaysModeledError(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.extendable.resources.ToNative.GetExtendableResourceErrorsOutput(result.dtor_value());
  }

  public GetExtendableResourceErrorsOutput LocalExtendableResourceAlwaysMultipleErrors(
      GetExtendableResourceErrorsInput nativeValue) {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput dafnyValue = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsInput(nativeValue);
    Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> result = this._impl.LocalExtendableResourceAlwaysMultipleErrors(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.extendable.resources.ToNative.GetExtendableResourceErrorsOutput(result.dtor_value());
  }

  public GetExtendableResourceErrorsOutput LocalExtendableResourceAlwaysNativeError(
      GetExtendableResourceErrorsInput nativeValue) {
    Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput dafnyValue = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsInput(nativeValue);
    Result<Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput, Error> result = this._impl.LocalExtendableResourceAlwaysNativeError(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return simple.extendable.resources.ToNative.GetExtendableResourceErrorsOutput(result.dtor_value());
  }

  protected ISimpleDependenciesClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder SimpleDependenciesConfig(SimpleDependenciesConfig SimpleDependenciesConfig);

    SimpleDependenciesConfig SimpleDependenciesConfig();

    SimpleDependencies build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleDependenciesConfig SimpleDependenciesConfig;

    protected BuilderImpl() {
    }

    public Builder SimpleDependenciesConfig(SimpleDependenciesConfig SimpleDependenciesConfig) {
      this.SimpleDependenciesConfig = SimpleDependenciesConfig;
      return this;
    }

    public SimpleDependenciesConfig SimpleDependenciesConfig() {
      return this.SimpleDependenciesConfig;
    }

    public SimpleDependencies build() {
      if (Objects.isNull(this.SimpleDependenciesConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `SimpleDependenciesConfig`");
      }
      return new SimpleDependencies(this);
    }
  }
}
