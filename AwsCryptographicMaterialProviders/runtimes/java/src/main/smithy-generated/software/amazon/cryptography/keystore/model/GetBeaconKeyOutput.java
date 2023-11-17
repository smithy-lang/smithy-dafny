// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Objects;

/**
 * Outputs for getting a Beacon Key
 */
public class GetBeaconKeyOutput {

  /**
   * The materials for the Beacon Key.
   */
  private final BeaconKeyMaterials beaconKeyMaterials;

  protected GetBeaconKeyOutput(BuilderImpl builder) {
    this.beaconKeyMaterials = builder.beaconKeyMaterials();
  }

  /**
   * @return The materials for the Beacon Key.
   */
  public BeaconKeyMaterials beaconKeyMaterials() {
    return this.beaconKeyMaterials;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param beaconKeyMaterials The materials for the Beacon Key.
     */
    Builder beaconKeyMaterials(BeaconKeyMaterials beaconKeyMaterials);

    /**
     * @return The materials for the Beacon Key.
     */
    BeaconKeyMaterials beaconKeyMaterials();

    GetBeaconKeyOutput build();
  }

  static class BuilderImpl implements Builder {

    protected BeaconKeyMaterials beaconKeyMaterials;

    protected BuilderImpl() {}

    protected BuilderImpl(GetBeaconKeyOutput model) {
      this.beaconKeyMaterials = model.beaconKeyMaterials();
    }

    public Builder beaconKeyMaterials(BeaconKeyMaterials beaconKeyMaterials) {
      this.beaconKeyMaterials = beaconKeyMaterials;
      return this;
    }

    public BeaconKeyMaterials beaconKeyMaterials() {
      return this.beaconKeyMaterials;
    }

    public GetBeaconKeyOutput build() {
      if (Objects.isNull(this.beaconKeyMaterials())) {
        throw new IllegalArgumentException(
          "Missing value for required field `beaconKeyMaterials`"
        );
      }
      return new GetBeaconKeyOutput(this);
    }
  }
}
