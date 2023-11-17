// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;

public class KeyVectorsConfig {

  private final String keyManifiestPath;

  protected KeyVectorsConfig(BuilderImpl builder) {
    this.keyManifiestPath = builder.keyManifiestPath();
  }

  public String keyManifiestPath() {
    return this.keyManifiestPath;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyManifiestPath(String keyManifiestPath);

    String keyManifiestPath();

    KeyVectorsConfig build();
  }

  static class BuilderImpl implements Builder {

    protected String keyManifiestPath;

    protected BuilderImpl() {}

    protected BuilderImpl(KeyVectorsConfig model) {
      this.keyManifiestPath = model.keyManifiestPath();
    }

    public Builder keyManifiestPath(String keyManifiestPath) {
      this.keyManifiestPath = keyManifiestPath;
      return this;
    }

    public String keyManifiestPath() {
      return this.keyManifiestPath;
    }

    public KeyVectorsConfig build() {
      if (Objects.isNull(this.keyManifiestPath())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyManifiestPath`"
        );
      }
      return new KeyVectorsConfig(this);
    }
  }
}
