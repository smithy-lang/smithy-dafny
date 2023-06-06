// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.nio.ByteBuffer;
import java.util.Objects;

/**
 * Outputs for getting a Branch Key's ACTIVE version.
 */
public class GetActiveBranchKeyOutput {
  /**
   * The ACTIVE Branch Key version.
   */
  private final String branchKeyVersion;

  /**
   * The key material for this ACTIVE Branch Key version.
   */
  private final ByteBuffer branchKey;

  protected GetActiveBranchKeyOutput(BuilderImpl builder) {
    this.branchKeyVersion = builder.branchKeyVersion();
    this.branchKey = builder.branchKey();
  }

  /**
   * @return The ACTIVE Branch Key version.
   */
  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  /**
   * @return The key material for this ACTIVE Branch Key version.
   */
  public ByteBuffer branchKey() {
    return this.branchKey;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param branchKeyVersion The ACTIVE Branch Key version.
     */
    Builder branchKeyVersion(String branchKeyVersion);

    /**
     * @return The ACTIVE Branch Key version.
     */
    String branchKeyVersion();

    /**
     * @param branchKey The key material for this ACTIVE Branch Key version.
     */
    Builder branchKey(ByteBuffer branchKey);

    /**
     * @return The key material for this ACTIVE Branch Key version.
     */
    ByteBuffer branchKey();

    GetActiveBranchKeyOutput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyVersion;

    protected ByteBuffer branchKey;

    protected BuilderImpl() {
    }

    protected BuilderImpl(GetActiveBranchKeyOutput model) {
      this.branchKeyVersion = model.branchKeyVersion();
      this.branchKey = model.branchKey();
    }

    public Builder branchKeyVersion(String branchKeyVersion) {
      this.branchKeyVersion = branchKeyVersion;
      return this;
    }

    public String branchKeyVersion() {
      return this.branchKeyVersion;
    }

    public Builder branchKey(ByteBuffer branchKey) {
      this.branchKey = branchKey;
      return this;
    }

    public ByteBuffer branchKey() {
      return this.branchKey;
    }

    public GetActiveBranchKeyOutput build() {
      if (Objects.isNull(this.branchKeyVersion()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKeyVersion`");
      }
      if (Objects.isNull(this.branchKey()))  {
        throw new IllegalArgumentException("Missing value for required field `branchKey`");
      }
      return new GetActiveBranchKeyOutput(this);
    }
  }
}
