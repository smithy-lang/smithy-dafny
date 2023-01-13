// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package example.simpletypes.model;

public class GetStringInput {
  private final String stringValue;

  protected GetStringInput(BuilderImpl builder) {
    this.stringValue = builder.stringValue();
  }

  public String stringValue() {
    return this.stringValue;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder stringValue(String stringValue);

    String stringValue();

    GetStringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String stringValue;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetStringInput model) {
      this.stringValue = model.stringValue();
    }

    public Builder stringValue(String stringValue) {
      this.stringValue = stringValue;
      return this;
    }

    public String stringValue() {
      return this.stringValue;
    }

    public GetStringInput build() {
      return new GetStringInput(this);
    }
  }
}
