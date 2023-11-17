// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;

public class BeaconKeyMaterials {

  private final String beaconKeyIdentifier;

  private final Map<String, String> encryptionContext;

  private final ByteBuffer beaconKey;

  private final Map<String, ByteBuffer> hmacKeys;

  protected BeaconKeyMaterials(BuilderImpl builder) {
    this.beaconKeyIdentifier = builder.beaconKeyIdentifier();
    this.encryptionContext = builder.encryptionContext();
    this.beaconKey = builder.beaconKey();
    this.hmacKeys = builder.hmacKeys();
  }

  public String beaconKeyIdentifier() {
    return this.beaconKeyIdentifier;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public ByteBuffer beaconKey() {
    return this.beaconKey;
  }

  public Map<String, ByteBuffer> hmacKeys() {
    return this.hmacKeys;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder beaconKeyIdentifier(String beaconKeyIdentifier);

    String beaconKeyIdentifier();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder beaconKey(ByteBuffer beaconKey);

    ByteBuffer beaconKey();

    Builder hmacKeys(Map<String, ByteBuffer> hmacKeys);

    Map<String, ByteBuffer> hmacKeys();

    BeaconKeyMaterials build();
  }

  static class BuilderImpl implements Builder {

    protected String beaconKeyIdentifier;

    protected Map<String, String> encryptionContext;

    protected ByteBuffer beaconKey;

    protected Map<String, ByteBuffer> hmacKeys;

    protected BuilderImpl() {}

    protected BuilderImpl(BeaconKeyMaterials model) {
      this.beaconKeyIdentifier = model.beaconKeyIdentifier();
      this.encryptionContext = model.encryptionContext();
      this.beaconKey = model.beaconKey();
      this.hmacKeys = model.hmacKeys();
    }

    public Builder beaconKeyIdentifier(String beaconKeyIdentifier) {
      this.beaconKeyIdentifier = beaconKeyIdentifier;
      return this;
    }

    public String beaconKeyIdentifier() {
      return this.beaconKeyIdentifier;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder beaconKey(ByteBuffer beaconKey) {
      this.beaconKey = beaconKey;
      return this;
    }

    public ByteBuffer beaconKey() {
      return this.beaconKey;
    }

    public Builder hmacKeys(Map<String, ByteBuffer> hmacKeys) {
      this.hmacKeys = hmacKeys;
      return this;
    }

    public Map<String, ByteBuffer> hmacKeys() {
      return this.hmacKeys;
    }

    public BeaconKeyMaterials build() {
      if (Objects.isNull(this.beaconKeyIdentifier())) {
        throw new IllegalArgumentException(
          "Missing value for required field `beaconKeyIdentifier`"
        );
      }
      if (Objects.isNull(this.encryptionContext())) {
        throw new IllegalArgumentException(
          "Missing value for required field `encryptionContext`"
        );
      }
      return new BeaconKeyMaterials(this);
    }
  }
}
