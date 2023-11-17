// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.nio.ByteBuffer;
import java.util.Objects;

public class GetKeyDescriptionInput {

  private final ByteBuffer json;

  protected GetKeyDescriptionInput(BuilderImpl builder) {
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

    GetKeyDescriptionInput build();
  }

  static class BuilderImpl implements Builder {

    protected ByteBuffer json;

    protected BuilderImpl() {}

    protected BuilderImpl(GetKeyDescriptionInput model) {
      this.json = model.json();
    }

    public Builder json(ByteBuffer json) {
      this.json = json;
      return this;
    }

    public ByteBuffer json() {
      return this.json;
    }

    public GetKeyDescriptionInput build() {
      if (Objects.isNull(this.json())) {
        throw new IllegalArgumentException(
          "Missing value for required field `json`"
        );
      }
      return new GetKeyDescriptionInput(this);
    }
  }
}
