// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies.wrapped;

import Dafny.Simple.Constraints.Types.GetConstraintsInput;
import Dafny.Simple.Constraints.Types.GetConstraintsOutput;
import Dafny.Simple.Dependencies.Types.Error;
import Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient;
import Dafny.Simple.Dependencies.Types.UseSimpleResourceInput;
import Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceDataInput;
import Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsInput;
import Dafny.Simple.Extendable.Resources.Types.GetExtendableResourceErrorsOutput;
import Dafny.Simple.Extendable.Resources.Types.UseExtendableResourceOutput;
import Dafny.Simple.Resources.Types.GetResourceDataOutput;
import Dafny.Simple.Resources.Types.GetResourcesInput;
import Dafny.Simple.Resources.Types.GetResourcesOutput;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import simple.dependencies.SimpleDependencies;
import simple.resources.ToDafny;
import simple.resources.ToNative;

public class TestSimpleDependencies implements ISimpleDependenciesClient {
  private final SimpleDependencies _impl;

  protected TestSimpleDependencies(BuilderImpl builder) {
    this._impl = builder.impl();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Result<GetResourcesOutput, Error> GetSimpleResource(GetResourcesInput dafnyInput) {
    simple.resources.model.GetResourcesInput nativeInput = ToNative.GetResourcesInput(dafnyInput);
    try {
      simple.resources.model.GetResourcesOutput nativeOutput = this._impl.GetSimpleResource(nativeInput);
      GetResourcesOutput dafnyOutput = ToDafny.GetResourcesOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<GetResourceDataOutput, Error> UseSimpleResource(UseSimpleResourceInput dafnyInput) {
    simple.dependencies.model.UseSimpleResourceInput nativeInput = simple.dependencies.ToNative.UseSimpleResourceInput(dafnyInput);
    try {
      simple.resources.model.GetResourceDataOutput nativeOutput = this._impl.UseSimpleResource(nativeInput);
      GetResourceDataOutput dafnyOutput = ToDafny.GetResourceDataOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<GetConstraintsOutput, Error> UseLocalConstraintsService(
      GetConstraintsInput dafnyInput) {
    simple.constraints.model.GetConstraintsInput nativeInput = simple.constraints.ToNative.GetConstraintsInput(dafnyInput);
    try {
      simple.constraints.model.GetConstraintsOutput nativeOutput = this._impl.UseLocalConstraintsService(nativeInput);
      GetConstraintsOutput dafnyOutput = simple.constraints.ToDafny.GetConstraintsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<UseExtendableResourceOutput, Error> UseLocalExtendableResource(
      GetExtendableResourceDataInput dafnyInput) {
    simple.extendable.resources.model.GetExtendableResourceDataInput nativeInput = simple.extendable.resources.ToNative.GetExtendableResourceDataInput(dafnyInput);
    try {
      simple.extendable.resources.model.UseExtendableResourceOutput nativeOutput = this._impl.UseLocalExtendableResource(nativeInput);
      UseExtendableResourceOutput dafnyOutput = simple.extendable.resources.ToDafny.UseExtendableResourceOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysModeledError(
      GetExtendableResourceErrorsInput dafnyInput) {
    simple.extendable.resources.model.GetExtendableResourceErrorsInput nativeInput = simple.extendable.resources.ToNative.GetExtendableResourceErrorsInput(dafnyInput);
    try {
      simple.extendable.resources.model.GetExtendableResourceErrorsOutput nativeOutput = this._impl.LocalExtendableResourceAlwaysModeledError(nativeInput);
      GetExtendableResourceErrorsOutput dafnyOutput = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysMultipleErrors(
      GetExtendableResourceErrorsInput dafnyInput) {
    simple.extendable.resources.model.GetExtendableResourceErrorsInput nativeInput = simple.extendable.resources.ToNative.GetExtendableResourceErrorsInput(dafnyInput);
    try {
      simple.extendable.resources.model.GetExtendableResourceErrorsOutput nativeOutput = this._impl.LocalExtendableResourceAlwaysMultipleErrors(nativeInput);
      GetExtendableResourceErrorsOutput dafnyOutput = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public Result<GetExtendableResourceErrorsOutput, Error> LocalExtendableResourceAlwaysNativeError(
      GetExtendableResourceErrorsInput dafnyInput) {
    simple.extendable.resources.model.GetExtendableResourceErrorsInput nativeInput = simple.extendable.resources.ToNative.GetExtendableResourceErrorsInput(dafnyInput);
    try {
      simple.extendable.resources.model.GetExtendableResourceErrorsOutput nativeOutput = this._impl.LocalExtendableResourceAlwaysNativeError(nativeInput);
      GetExtendableResourceErrorsOutput dafnyOutput = simple.extendable.resources.ToDafny.GetExtendableResourceErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (RuntimeException ex) {
      return Result.create_Failure(simple.dependencies.ToDafny.Error(ex));
    }
  }

  public interface Builder {
    Builder impl(SimpleDependencies impl);

    SimpleDependencies impl();

    TestSimpleDependencies build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleDependencies impl;

    protected BuilderImpl() {
    }

    public Builder impl(SimpleDependencies impl) {
      this.impl = impl;
      return this;
    }

    public SimpleDependencies impl() {
      return this.impl;
    }

    public TestSimpleDependencies build() {
      if (Objects.isNull(this.impl()))  {
        throw new IllegalArgumentException("Missing value for required field `impl`");
      }
      return new TestSimpleDependencies(this);
    }
  }
}
