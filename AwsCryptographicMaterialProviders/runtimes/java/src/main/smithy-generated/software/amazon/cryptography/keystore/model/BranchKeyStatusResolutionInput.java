// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be
// overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Objects;

/** Inputs for resolving a multiple ACTIVE versions state. */
public class BranchKeyStatusResolutionInput {

  /** The identifier for the Branch Key which has more than one ACTIVE version */
  private final String branchKeyIdentifier;

  protected BranchKeyStatusResolutionInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
  }

  /**
   * @return The identifier for the Branch Key which has more than one ACTIVE version
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
     * @param branchKeyIdentifier The identifier for the Branch Key which has more than one ACTIVE
     *     version
     */
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    /**
     * @return The identifier for the Branch Key which has more than one ACTIVE version
     */
    String branchKeyIdentifier();

    BranchKeyStatusResolutionInput build();
  }

  static class BuilderImpl implements Builder {

    protected String branchKeyIdentifier;

    protected BuilderImpl() {}

    protected BuilderImpl(BranchKeyStatusResolutionInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public BranchKeyStatusResolutionInput build() {
      if (Objects.isNull(this.branchKeyIdentifier())) {
        throw new IllegalArgumentException(
          "Missing value for required field `branchKeyIdentifier`"
        );
      }
      return new BranchKeyStatusResolutionInput(this);
    }
  }
}
