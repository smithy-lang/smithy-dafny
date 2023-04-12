// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.errors.wrapped;

import Dafny.Simple.Errors.Types.Error;
import Dafny.Simple.Errors.Types.GetErrorsInput;
import Dafny.Simple.Errors.Types.GetErrorsOutput;
import Dafny.Simple.Errors.Types.ISimpleErrorsClient;
import Wrappers_Compile.Result;
import java.lang.Exception;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import simple.errors.SimpleErrors;
import simple.errors.ToDafny;
import simple.errors.ToNative;
import simple.errors.model.NativeError;
import simple.errors.model.OpaqueError;

public class TestSimpleErrors implements ISimpleErrorsClient {
  private final SimpleErrors _impl;

  protected TestSimpleErrors(BuilderImpl builder) {
    this._impl = builder.impl();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Result<GetErrorsOutput, Error> AlwaysError(GetErrorsInput dafnyInput) {
    simple.errors.model.GetErrorsInput nativeInput = ToNative.GetErrorsInput(dafnyInput);
    try {
      simple.errors.model.GetErrorsOutput nativeOutput = this._impl.AlwaysError(nativeInput);
      GetErrorsOutput dafnyOutput = ToDafny.GetErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (NativeError ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<GetErrorsOutput, Error> AlwaysMultipleErrors(GetErrorsInput dafnyInput) {
    simple.errors.model.GetErrorsInput nativeInput = ToNative.GetErrorsInput(dafnyInput);
    try {
      simple.errors.model.GetErrorsOutput nativeOutput = this._impl.AlwaysMultipleErrors(nativeInput);
      GetErrorsOutput dafnyOutput = ToDafny.GetErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (NativeError ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public Result<GetErrorsOutput, Error> AlwaysNativeError(GetErrorsInput dafnyInput) {
    simple.errors.model.GetErrorsInput nativeInput = ToNative.GetErrorsInput(dafnyInput);
    try {
      simple.errors.model.GetErrorsOutput nativeOutput = this._impl.AlwaysNativeError(nativeInput);
      GetErrorsOutput dafnyOutput = ToDafny.GetErrorsOutput(nativeOutput);
      return Result.create_Success(dafnyOutput);
    } catch (NativeError ex) {
      return Result.create_Failure(ToDafny.Error(ex));
    } catch (Exception ex) {
      OpaqueError error = OpaqueError.builder().obj(ex).cause(ex).build();
      return Result.create_Failure(ToDafny.Error(error));
    }
  }

  public interface Builder {
    Builder impl(SimpleErrors impl);

    SimpleErrors impl();

    TestSimpleErrors build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleErrors impl;

    protected BuilderImpl() {
    }

    public Builder impl(SimpleErrors impl) {
      this.impl = impl;
      return this;
    }

    public SimpleErrors impl() {
      return this.impl;
    }

    public TestSimpleErrors build() {
      if (Objects.isNull(this.impl()))  {
        throw new IllegalArgumentException("Missing value for required field `impl`");
      }
      return new TestSimpleErrors(this);
    }
  }
}
