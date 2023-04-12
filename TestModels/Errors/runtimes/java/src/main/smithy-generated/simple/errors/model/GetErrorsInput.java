// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.errors.model;

public class GetErrorsInput {
  private final String value;

  protected GetErrorsInput(BuilderImpl builder) {
    this.value = builder.value();
  }

  public String value() {
    return this.value;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder value(String value);

    String value();

    GetErrorsInput build();
  }

  static class BuilderImpl implements Builder {
    protected String value;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetErrorsInput model) {
      this.value = model.value();
    }

    public Builder value(String value) {
      this.value = value;
      return this;
    }

    public String value() {
      return this.value;
    }

    public GetErrorsInput build() {
      return new GetErrorsInput(this);
    }
  }
}
