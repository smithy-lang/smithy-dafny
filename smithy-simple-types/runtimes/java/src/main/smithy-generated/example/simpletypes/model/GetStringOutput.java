// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package example.simpletypes.model;

public class GetStringOutput {
  private final String result;

  protected GetStringOutput(BuilderImpl builder) {
    this.result = builder.result();
  }

  public String result() {
    return this.result;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder result(String result);

    String result();

    GetStringOutput build();
  }

  static class BuilderImpl implements Builder {
    protected String result;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetStringOutput model) {
      this.result = model.result();
    }

    public Builder result(String result) {
      this.result = result;
      return this;
    }

    public String result() {
      return this.result;
    }

    public GetStringOutput build() {
      return new GetStringOutput(this);
    }
  }
}
