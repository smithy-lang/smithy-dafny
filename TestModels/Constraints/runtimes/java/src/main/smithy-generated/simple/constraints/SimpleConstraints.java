// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.util.Objects;
import simple.constraints.internaldafny.SimpleConstraintsClient;
import simple.constraints.internaldafny.__default;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;
import simple.constraints.model.GetConstraintsInput;
import simple.constraints.model.GetConstraintsOutput;
import simple.constraints.model.SimpleConstraintsConfig;

public class SimpleConstraints {

  private final ISimpleConstraintsClient _impl;

  protected SimpleConstraints(BuilderImpl builder) {
    SimpleConstraintsConfig input = builder.SimpleConstraintsConfig();
    simple.constraints.internaldafny.types.SimpleConstraintsConfig dafnyValue =
      ToDafny.SimpleConstraintsConfig(input);
    Result<SimpleConstraintsClient, Error> result = __default.SimpleConstraints(
      dafnyValue
    );
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    this._impl = result.dtor_value();
  }

  SimpleConstraints(ISimpleConstraintsClient impl) {
    this._impl = impl;
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public GetConstraintsOutput GetConstraints(GetConstraintsInput input) {
    simple.constraints.internaldafny.types.GetConstraintsInput dafnyValue =
      ToDafny.GetConstraintsInput(input);
    Result<
      simple.constraints.internaldafny.types.GetConstraintsOutput,
      Error
    > result = this._impl.GetConstraints(dafnyValue);
    if (result.is_Failure()) {
      throw ToNative.Error(result.dtor_error());
    }
    return ToNative.GetConstraintsOutput(result.dtor_value());
  }

  protected ISimpleConstraintsClient impl() {
    return this._impl;
  }

  public interface Builder {
    Builder SimpleConstraintsConfig(
      SimpleConstraintsConfig SimpleConstraintsConfig
    );

    SimpleConstraintsConfig SimpleConstraintsConfig();

    SimpleConstraints build();
  }

  static class BuilderImpl implements Builder {

    protected SimpleConstraintsConfig SimpleConstraintsConfig;

    protected BuilderImpl() {}

    public Builder SimpleConstraintsConfig(
      SimpleConstraintsConfig SimpleConstraintsConfig
    ) {
      this.SimpleConstraintsConfig = SimpleConstraintsConfig;
      return this;
    }

    public SimpleConstraintsConfig SimpleConstraintsConfig() {
      return this.SimpleConstraintsConfig;
    }

    public SimpleConstraints build() {
      if (Objects.isNull(this.SimpleConstraintsConfig())) {
        throw new IllegalArgumentException(
          "Missing value for required field `SimpleConstraintsConfig`"
        );
      }
      return new SimpleConstraints(this);
    }
  }
}
