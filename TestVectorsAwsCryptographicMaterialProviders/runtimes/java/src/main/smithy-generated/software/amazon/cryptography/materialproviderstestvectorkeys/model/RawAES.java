// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;

public class RawAES {

  private final String keyId;

  private final String providerId;

  protected RawAES(BuilderImpl builder) {
    this.keyId = builder.keyId();
    this.providerId = builder.providerId();
  }

  public String keyId() {
    return this.keyId;
  }

  public String providerId() {
    return this.providerId;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyId(String keyId);

    String keyId();

    Builder providerId(String providerId);

    String providerId();

    RawAES build();
  }

  static class BuilderImpl implements Builder {

    protected String keyId;

    protected String providerId;

    protected BuilderImpl() {}

    protected BuilderImpl(RawAES model) {
      this.keyId = model.keyId();
      this.providerId = model.providerId();
    }

    public Builder keyId(String keyId) {
      this.keyId = keyId;
      return this;
    }

    public String keyId() {
      return this.keyId;
    }

    public Builder providerId(String providerId) {
      this.providerId = providerId;
      return this;
    }

    public String providerId() {
      return this.providerId;
    }

    public RawAES build() {
      if (Objects.isNull(this.keyId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyId`"
        );
      }
      if (Objects.isNull(this.providerId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `providerId`"
        );
      }
      return new RawAES(this);
    }
  }
}
