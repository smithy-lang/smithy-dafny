// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies.model;

import java.util.Objects;
import simple.resources.ISimpleResource;
import simple.resources.SimpleResource;
import simple.resources.model.GetResourceDataInput;

public class UseSimpleResourceInput {
  private final ISimpleResource value;

  private final GetResourceDataInput input;

  protected UseSimpleResourceInput(BuilderImpl builder) {
    this.value = builder.value();
    this.input = builder.input();
  }

  public ISimpleResource value() {
    return this.value;
  }

  public GetResourceDataInput input() {
    return this.input;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder value(ISimpleResource value);

    ISimpleResource value();

    Builder input(GetResourceDataInput input);

    GetResourceDataInput input();

    UseSimpleResourceInput build();
  }

  static class BuilderImpl implements Builder {
    protected ISimpleResource value;

    protected GetResourceDataInput input;

    protected BuilderImpl() {
    }

    protected BuilderImpl(UseSimpleResourceInput model) {
      this.value = model.value();
      this.input = model.input();
    }

    public Builder value(ISimpleResource value) {
      this.value = SimpleResource.wrap(value);
      return this;
    }

    public ISimpleResource value() {
      return this.value;
    }

    public Builder input(GetResourceDataInput input) {
      this.input = input;
      return this;
    }

    public GetResourceDataInput input() {
      return this.input;
    }

    public UseSimpleResourceInput build() {
      if (Objects.isNull(this.value()))  {
        throw new IllegalArgumentException("Missing value for required field `value`");
      }
      if (Objects.isNull(this.input()))  {
        throw new IllegalArgumentException("Missing value for required field `input`");
      }
      return new UseSimpleResourceInput(this);
    }
  }
}
