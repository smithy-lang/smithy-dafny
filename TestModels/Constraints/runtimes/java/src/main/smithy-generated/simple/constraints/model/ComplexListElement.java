// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.constraints.model;

import java.nio.ByteBuffer;

public class ComplexListElement {
  private final String value;

  private final ByteBuffer blob;

  protected ComplexListElement(BuilderImpl builder) {
    this.value = builder.value();
    this.blob = builder.blob();
  }

  public String value() {
    return this.value;
  }

  public ByteBuffer blob() {
    return this.blob;
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

    Builder blob(ByteBuffer blob);

    ByteBuffer blob();

    ComplexListElement build();
  }

  static class BuilderImpl implements Builder {
    protected String value;

    protected ByteBuffer blob;

    protected BuilderImpl() {
    }

    protected BuilderImpl(ComplexListElement model) {
      this.value = model.value();
      this.blob = model.blob();
    }

    public Builder value(String value) {
      this.value = value;
      return this;
    }

    public String value() {
      return this.value;
    }

    public Builder blob(ByteBuffer blob) {
      this.blob = blob;
      return this;
    }

    public ByteBuffer blob() {
      return this.blob;
    }

    public ComplexListElement build() {
      return new ComplexListElement(this);
    }
  }
}
