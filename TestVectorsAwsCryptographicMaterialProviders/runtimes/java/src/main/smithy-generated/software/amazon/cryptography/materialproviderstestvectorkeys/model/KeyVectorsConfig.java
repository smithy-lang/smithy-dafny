// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;

public class KeyVectorsConfig {

  private final String keyManifestPath;

  protected KeyVectorsConfig(BuilderImpl builder) {
    this.keyManifestPath = builder.keyManifestPath();
  }

  public String keyManifestPath() {
    return this.keyManifestPath;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyManifestPath(String keyManifestPath);

    String keyManifestPath();

    KeyVectorsConfig build();
  }

  static class BuilderImpl implements Builder {

    protected String keyManifestPath;

    protected BuilderImpl() {}

    protected BuilderImpl(KeyVectorsConfig model) {
      this.keyManifestPath = model.keyManifestPath();
    }

    public Builder keyManifestPath(String keyManifestPath) {
      this.keyManifestPath = keyManifestPath;
      return this;
    }

    public String keyManifestPath() {
      return this.keyManifestPath;
    }

    public KeyVectorsConfig build() {
      if (Objects.isNull(this.keyManifestPath())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyManifestPath`"
        );
      }
      return new KeyVectorsConfig(this);
    }
  }
}
