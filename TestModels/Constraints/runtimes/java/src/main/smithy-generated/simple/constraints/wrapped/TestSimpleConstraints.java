// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints.wrapped;

import Wrappers_Compile.Result;
import java.lang.IllegalArgumentException;
import java.lang.RuntimeException;
import java.util.Objects;
import simple.constraints.SimpleConstraints;
import simple.constraints.ToDafny;
import simple.constraints.ToNative;
import simple.constraints.internaldafny.types.Error;
import simple.constraints.internaldafny.types.GetConstraintsInput;
import simple.constraints.internaldafny.types.GetConstraintsOutput;
import simple.constraints.internaldafny.types.ISimpleConstraintsClient;

public class TestSimpleConstraints implements ISimpleConstraintsClient {

  private final SimpleConstraints _impl;

  protected TestSimpleConstraints(BuilderImpl builder) {
    this._impl = builder.impl();
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public Result<GetConstraintsOutput, Error> GetConstraints(
    GetConstraintsInput dafnyInput
  ) {
    try {
      simple.constraints.model.GetConstraintsInput nativeInput =
        ToNative.GetConstraintsInput(dafnyInput);
      simple.constraints.model.GetConstraintsOutput nativeOutput =
        this._impl.GetConstraints(nativeInput);
      GetConstraintsOutput dafnyOutput = ToDafny.GetConstraintsOutput(
        nativeOutput
      );
      return Result.create_Success(
        GetConstraintsOutput._typeDescriptor(),
        Error._typeDescriptor(),
        dafnyOutput
      );
    } catch (RuntimeException ex) {
      return Result.create_Failure(
        GetConstraintsOutput._typeDescriptor(),
        Error._typeDescriptor(),
        ToDafny.Error(ex)
      );
    }
  }

  public interface Builder {
    Builder impl(SimpleConstraints impl);

    SimpleConstraints impl();

    TestSimpleConstraints build();
  }

  static class BuilderImpl implements Builder {

    protected SimpleConstraints impl;

    protected BuilderImpl() {}

    public Builder impl(SimpleConstraints impl) {
      this.impl = impl;
      return this;
    }

    public SimpleConstraints impl() {
      return this.impl;
    }

    public TestSimpleConstraints build() {
      if (Objects.isNull(this.impl())) {
        throw new IllegalArgumentException(
          "Missing value for required field `impl`"
        );
      }
      return new TestSimpleConstraints(this);
    }
  }
}
