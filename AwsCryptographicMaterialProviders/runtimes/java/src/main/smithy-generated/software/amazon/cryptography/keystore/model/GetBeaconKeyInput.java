// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Objects;

/**
 * Inputs for getting a Beacon Key
 */
public class GetBeaconKeyInput {

  /**
   * The identifier of the Branch Key the Beacon Key is associated with.
   */
  private final String branchKeyIdentifier;

  protected GetBeaconKeyInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
  }

  /**
   * @return The identifier of the Branch Key the Beacon Key is associated with.
   */
  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param branchKeyIdentifier The identifier of the Branch Key the Beacon Key is associated with.
     */
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    /**
     * @return The identifier of the Branch Key the Beacon Key is associated with.
     */
    String branchKeyIdentifier();

    GetBeaconKeyInput build();
  }

  static class BuilderImpl implements Builder {

    protected String branchKeyIdentifier;

    protected BuilderImpl() {}

    protected BuilderImpl(GetBeaconKeyInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public GetBeaconKeyInput build() {
      if (Objects.isNull(this.branchKeyIdentifier())) {
        throw new IllegalArgumentException(
          "Missing value for required field `branchKeyIdentifier`"
        );
      }
      return new GetBeaconKeyInput(this);
    }
  }
}
