// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.List;
import java.util.Objects;

public class RequiredEncryptionContextCMM {

  private final KeyDescription underlying;

  private final List<String> requiredEncryptionContextKeys;

  protected RequiredEncryptionContextCMM(BuilderImpl builder) {
    this.underlying = builder.underlying();
    this.requiredEncryptionContextKeys =
      builder.requiredEncryptionContextKeys();
  }

  public KeyDescription underlying() {
    return this.underlying;
  }

  public List<String> requiredEncryptionContextKeys() {
    return this.requiredEncryptionContextKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder underlying(KeyDescription underlying);

    KeyDescription underlying();

    Builder requiredEncryptionContextKeys(
      List<String> requiredEncryptionContextKeys
    );

    List<String> requiredEncryptionContextKeys();

    RequiredEncryptionContextCMM build();
  }

  static class BuilderImpl implements Builder {

    protected KeyDescription underlying;

    protected List<String> requiredEncryptionContextKeys;

    protected BuilderImpl() {}

    protected BuilderImpl(RequiredEncryptionContextCMM model) {
      this.underlying = model.underlying();
      this.requiredEncryptionContextKeys =
        model.requiredEncryptionContextKeys();
    }

    public Builder underlying(KeyDescription underlying) {
      this.underlying = underlying;
      return this;
    }

    public KeyDescription underlying() {
      return this.underlying;
    }

    public Builder requiredEncryptionContextKeys(
      List<String> requiredEncryptionContextKeys
    ) {
      this.requiredEncryptionContextKeys = requiredEncryptionContextKeys;
      return this;
    }

    public List<String> requiredEncryptionContextKeys() {
      return this.requiredEncryptionContextKeys;
    }

    public RequiredEncryptionContextCMM build() {
      if (Objects.isNull(this.underlying())) {
        throw new IllegalArgumentException(
          "Missing value for required field `underlying`"
        );
      }
      if (Objects.isNull(this.requiredEncryptionContextKeys())) {
        throw new IllegalArgumentException(
          "Missing value for required field `requiredEncryptionContextKeys`"
        );
      }
      return new RequiredEncryptionContextCMM(this);
    }
  }
}
