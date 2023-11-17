// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Objects;

/**
 * Inputs for getting a version of a Branch Key.
 */
public class GetBranchKeyVersionInput {

  /**
   * The identifier for the Branch Key to get a particular version for.
   */
  private final String branchKeyIdentifier;

  /**
   * The version to get.
   */
  private final String branchKeyVersion;

  protected GetBranchKeyVersionInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.branchKeyVersion = builder.branchKeyVersion();
  }

  /**
   * @return The identifier for the Branch Key to get a particular version for.
   */
  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  /**
   * @return The version to get.
   */
  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param branchKeyIdentifier The identifier for the Branch Key to get a particular version for.
     */
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    /**
     * @return The identifier for the Branch Key to get a particular version for.
     */
    String branchKeyIdentifier();

    /**
     * @param branchKeyVersion The version to get.
     */
    Builder branchKeyVersion(String branchKeyVersion);

    /**
     * @return The version to get.
     */
    String branchKeyVersion();

    GetBranchKeyVersionInput build();
  }

  static class BuilderImpl implements Builder {

    protected String branchKeyIdentifier;

    protected String branchKeyVersion;

    protected BuilderImpl() {}

    protected BuilderImpl(GetBranchKeyVersionInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.branchKeyVersion = model.branchKeyVersion();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public Builder branchKeyVersion(String branchKeyVersion) {
      this.branchKeyVersion = branchKeyVersion;
      return this;
    }

    public String branchKeyVersion() {
      return this.branchKeyVersion;
    }

    public GetBranchKeyVersionInput build() {
      if (Objects.isNull(this.branchKeyIdentifier())) {
        throw new IllegalArgumentException(
          "Missing value for required field `branchKeyIdentifier`"
        );
      }
      if (Objects.isNull(this.branchKeyVersion())) {
        throw new IllegalArgumentException(
          "Missing value for required field `branchKeyVersion`"
        );
      }
      return new GetBranchKeyVersionInput(this);
    }
  }
}
