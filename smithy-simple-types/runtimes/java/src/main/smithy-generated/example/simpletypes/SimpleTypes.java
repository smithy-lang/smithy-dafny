// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package example.simpletypes;

import Dafny.Example.Simpletypes.SimpleTypesClient;
import Dafny.Example.Simpletypes.Types.Error;
import Dafny.Example.Simpletypes.Types.ISimpleTypesServiceClient;
import Dafny.Example.Simpletypes.__default;
import Wrappers_Compile.Result;
import example.simpletypes.model.EmptyConfig;
import example.simpletypes.model.GetStringInput;
import example.simpletypes.model.GetStringOutput;
import java.lang.IllegalArgumentException;
import java.util.Objects;

public class SimpleTypes {
  private final ISimpleTypesServiceClient _impl;

  protected SimpleTypes(BuilderImpl builder) {
    EmptyConfig nativeValue = builder.EmptyConfig();
    Dafny.Example.Simpletypes.Types.EmptyConfig dafnyValue = ToDafny.EmptyConfig(nativeValue);
    Result<SimpleTypesClient, Error> result = __default.SimpleTypes(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public GetStringOutput GetString(GetStringInput nativeValue) {
    Dafny.Example.Simpletypes.Types.GetStringInput dafnyValue = ToDafny.GetStringInput(nativeValue);
    Result<Dafny.Example.Simpletypes.Types.GetStringOutput, Error> result = this._impl.GetString(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetStringOutput(result.dtor_value());
  }

  public interface Builder {
    Builder EmptyConfig(EmptyConfig EmptyConfig);

    EmptyConfig EmptyConfig();

    SimpleTypes build();
  }

  static class BuilderImpl implements Builder {
    protected EmptyConfig EmptyConfig;

    protected BuilderImpl() {
    }

    public Builder EmptyConfig(EmptyConfig EmptyConfig) {
      this.EmptyConfig = EmptyConfig;
      return this;
    }

    public EmptyConfig EmptyConfig() {
      return this.EmptyConfig;
    }

    public SimpleTypes build() {
      if (Objects.isNull(this.EmptyConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `EmptyConfig`");
      }
      return new SimpleTypes(this);
    }
  }
}
