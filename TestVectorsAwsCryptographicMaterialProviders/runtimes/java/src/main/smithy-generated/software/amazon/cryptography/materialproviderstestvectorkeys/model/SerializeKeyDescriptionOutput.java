// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class SerializeKeyDescriptionOutput {

  private final ByteBuffer json;

  protected SerializeKeyDescriptionOutput(BuilderImpl builder) {
    this.json = builder.json();
  }

  public ByteBuffer json() {
    return this.json;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder json(ByteBuffer json);

    ByteBuffer json();

    SerializeKeyDescriptionOutput build();
  }

  static class BuilderImpl implements Builder {

    protected ByteBuffer json;

    protected BuilderImpl() {}

    protected BuilderImpl(SerializeKeyDescriptionOutput model) {
      this.json = model.json();
    }

    public Builder json(ByteBuffer json) {
      this.json = json;
      return this;
    }

    public ByteBuffer json() {
      return this.json;
    }

    public SerializeKeyDescriptionOutput build() {
      if (Objects.isNull(this.json())) {
        throw new IllegalArgumentException(
          "Missing value for required field `json`"
        );
      }
      return new SerializeKeyDescriptionOutput(this);
    }
  }
}
