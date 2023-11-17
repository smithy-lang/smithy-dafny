// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;
import software.amazon.cryptography.materialproviders.model.PaddingScheme;

public class RawRSA {

  private final String keyId;

  private final String providerId;

  private final PaddingScheme padding;

  protected RawRSA(BuilderImpl builder) {
    this.keyId = builder.keyId();
    this.providerId = builder.providerId();
    this.padding = builder.padding();
  }

  public String keyId() {
    return this.keyId;
  }

  public String providerId() {
    return this.providerId;
  }

  public PaddingScheme padding() {
    return this.padding;
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

    Builder padding(PaddingScheme padding);

    PaddingScheme padding();

    RawRSA build();
  }

  static class BuilderImpl implements Builder {

    protected String keyId;

    protected String providerId;

    protected PaddingScheme padding;

    protected BuilderImpl() {}

    protected BuilderImpl(RawRSA model) {
      this.keyId = model.keyId();
      this.providerId = model.providerId();
      this.padding = model.padding();
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

    public Builder padding(PaddingScheme padding) {
      this.padding = padding;
      return this;
    }

    public PaddingScheme padding() {
      return this.padding;
    }

    public RawRSA build() {
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
      if (Objects.isNull(this.padding())) {
        throw new IllegalArgumentException(
          "Missing value for required field `padding`"
        );
      }
      return new RawRSA(this);
    }
  }
}
