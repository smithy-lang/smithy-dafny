// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.nio.ByteBuffer;
import java.util.Objects;

/**
 * Outputs for getting a Beacon Key
 */
public class GetBeaconKeyOutput {
  /**
   * The identifier for the Beacon Key.
   */
  private final String beaconKeyIdentifier;

  /**
   * The key material for this Beacon Key.
   */
  private final ByteBuffer beaconKey;

  protected GetBeaconKeyOutput(BuilderImpl builder) {
    this.beaconKeyIdentifier = builder.beaconKeyIdentifier();
    this.beaconKey = builder.beaconKey();
  }

  /**
   * @return The identifier for the Beacon Key.
   */
  public String beaconKeyIdentifier() {
    return this.beaconKeyIdentifier;
  }

  /**
   * @return The key material for this Beacon Key.
   */
  public ByteBuffer beaconKey() {
    return this.beaconKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param beaconKeyIdentifier The identifier for the Beacon Key.
     */
    Builder beaconKeyIdentifier(String beaconKeyIdentifier);

    /**
     * @return The identifier for the Beacon Key.
     */
    String beaconKeyIdentifier();

    /**
     * @param beaconKey The key material for this Beacon Key.
     */
    Builder beaconKey(ByteBuffer beaconKey);

    /**
     * @return The key material for this Beacon Key.
     */
    ByteBuffer beaconKey();

    GetBeaconKeyOutput build();
  }

  static class BuilderImpl implements Builder {
    protected String beaconKeyIdentifier;

    protected ByteBuffer beaconKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetBeaconKeyOutput model) {
      this.beaconKeyIdentifier = model.beaconKeyIdentifier();
      this.beaconKey = model.beaconKey();
    }

    public Builder beaconKeyIdentifier(String beaconKeyIdentifier) {
      this.beaconKeyIdentifier = beaconKeyIdentifier;
      return this;
    }

    public String beaconKeyIdentifier() {
      return this.beaconKeyIdentifier;
    }

    public Builder beaconKey(ByteBuffer beaconKey) {
      this.beaconKey = beaconKey;
      return this;
    }

    public ByteBuffer beaconKey() {
      return this.beaconKey;
    }

    public GetBeaconKeyOutput build() {
      if (Objects.isNull(this.beaconKeyIdentifier()))  {
        throw new IllegalArgumentException("Missing value for required field `beaconKeyIdentifier`");
      }
      if (Objects.isNull(this.beaconKey()))  {
        throw new IllegalArgumentException("Missing value for required field `beaconKey`");
      }
      return new GetBeaconKeyOutput(this);
    }
  }
}
