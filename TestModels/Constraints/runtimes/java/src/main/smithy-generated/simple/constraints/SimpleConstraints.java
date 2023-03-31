// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints;

import Dafny.Simple.Constraints.SimpleConstraintsClient;
import Dafny.Simple.Constraints.Types.Error;
import Dafny.Simple.Constraints.Types.ISimpleConstraintsClient;
import Dafny.Simple.Constraints.__default;
import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import simple.constraints.model.GetConstraintsInput;
import simple.constraints.model.GetConstraintsOutput;
import simple.constraints.model.SimpleConstraintsConfig;

public class SimpleConstraints {
  private final ISimpleConstraintsClient _impl;

  protected SimpleConstraints(BuilderImpl builder) {
    SimpleConstraintsConfig nativeValue = builder.SimpleConstraintsConfig();
    Dafny.Simple.Constraints.Types.SimpleConstraintsConfig dafnyValue = ToDafny.SimpleConstraintsConfig(nativeValue);
    Result<SimpleConstraintsClient, Error> result = __default.SimpleConstraints(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public GetConstraintsOutput GetConstraints(GetConstraintsInput nativeValue) {
    Dafny.Simple.Constraints.Types.GetConstraintsInput dafnyValue = ToDafny.GetConstraintsInput(nativeValue);
    Result<Dafny.Simple.Constraints.Types.GetConstraintsOutput, Error> result = this._impl.GetConstraints(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetConstraintsOutput(result.dtor_value());
  }

  protected ISimpleConstraintsClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder SimpleConstraintsConfig(SimpleConstraintsConfig SimpleConstraintsConfig);

    SimpleConstraintsConfig SimpleConstraintsConfig();

    SimpleConstraints build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleConstraintsConfig SimpleConstraintsConfig;

    protected BuilderImpl() {
    }

    public Builder SimpleConstraintsConfig(SimpleConstraintsConfig SimpleConstraintsConfig) {
      this.SimpleConstraintsConfig = SimpleConstraintsConfig;
      return this;
    }

    public SimpleConstraintsConfig SimpleConstraintsConfig() {
      return this.SimpleConstraintsConfig;
    }

    public SimpleConstraints build() {
      if (Objects.isNull(this.SimpleConstraintsConfig()))  {
        throw new IllegalArgumentException("Missing value for required field `SimpleConstraintsConfig`");
      }
      return new SimpleConstraints(this);
    }
  }
}
