// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.errors;

import Dafny.Simple.Errors.SimpleErrorsClient;
import Dafny.Simple.Errors.Types.Error;
import Dafny.Simple.Errors.Types.ISimpleErrorsClient;
import Dafny.Simple.Errors.__default;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import simple.errors.model.GetErrorsInput;
import simple.errors.model.GetErrorsOutput;
import simple.errors.model.SimpleErrorsConfig;

public class SimpleErrors {
  private final ISimpleErrorsClient _impl;

  protected SimpleErrors(BuilderImpl builder) {
    SimpleErrorsConfig nativeValue = builder.SimpleErrorsConfig();
    Dafny.Simple.Errors.Types.SimpleErrorsConfig dafnyValue = ToDafny.SimpleErrorsConfig(nativeValue);
    Result<SimpleErrorsClient, Error> result = __default.SimpleErrors(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public GetErrorsOutput AlwaysError(GetErrorsInput nativeValue) {
    Dafny.Simple.Errors.Types.GetErrorsInput dafnyValue = ToDafny.GetErrorsInput(nativeValue);
    Result<Dafny.Simple.Errors.Types.GetErrorsOutput, Error> result = this._impl.AlwaysError(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetErrorsOutput(result.dtor_value());
  }

  public GetErrorsOutput AlwaysMultipleErrors(GetErrorsInput nativeValue) {
    Dafny.Simple.Errors.Types.GetErrorsInput dafnyValue = ToDafny.GetErrorsInput(nativeValue);
    Result<Dafny.Simple.Errors.Types.GetErrorsOutput, Error> result = this._impl.AlwaysMultipleErrors(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetErrorsOutput(result.dtor_value());
  }

  public GetErrorsOutput AlwaysNativeError(GetErrorsInput nativeValue) {
    Dafny.Simple.Errors.Types.GetErrorsInput dafnyValue = ToDafny.GetErrorsInput(nativeValue);
    Result<Dafny.Simple.Errors.Types.GetErrorsOutput, Error> result = this._impl.AlwaysNativeError(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetErrorsOutput(result.dtor_value());
  }

  protected ISimpleErrorsClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder SimpleErrorsConfig(SimpleErrorsConfig SimpleErrorsConfig);

    SimpleErrorsConfig SimpleErrorsConfig();

    SimpleErrors build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleErrorsConfig SimpleErrorsConfig;

    protected BuilderImpl() {
    }

    public Builder SimpleErrorsConfig(SimpleErrorsConfig SimpleErrorsConfig) {
      this.SimpleErrorsConfig = SimpleErrorsConfig;
      return this;
    }

    public SimpleErrorsConfig SimpleErrorsConfig() {
      return this.SimpleErrorsConfig;
    }

    public SimpleErrors build() {
      if (Objects.isNull(this.SimpleErrorsConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `SimpleErrorsConfig`");
      }
      return new SimpleErrors(this);
    }
  }
}
