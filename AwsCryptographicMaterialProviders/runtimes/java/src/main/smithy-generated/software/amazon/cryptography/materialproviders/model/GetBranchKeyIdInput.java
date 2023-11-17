// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Map;
import java.util.Objects;

/**
 * Inputs for determining the Branch Key which should be used to wrap or unwrap the data key for this encryption or decryption
 */
public class GetBranchKeyIdInput {

  /**
   * The Encryption Context used with this encryption or decryption.
   */
  private final Map<String, String> encryptionContext;

  protected GetBranchKeyIdInput(BuilderImpl builder) {
    this.encryptionContext = builder.encryptionContext();
  }

  /**
   * @return The Encryption Context used with this encryption or decryption.
   */
  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param encryptionContext The Encryption Context used with this encryption or decryption.
     */
    Builder encryptionContext(Map<String, String> encryptionContext);

    /**
     * @return The Encryption Context used with this encryption or decryption.
     */
    Map<String, String> encryptionContext();

    GetBranchKeyIdInput build();
  }

  static class BuilderImpl implements Builder {

    protected Map<String, String> encryptionContext;

    protected BuilderImpl() {}

    protected BuilderImpl(GetBranchKeyIdInput model) {
      this.encryptionContext = model.encryptionContext();
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public GetBranchKeyIdInput build() {
      if (Objects.isNull(this.encryptionContext())) {
        throw new IllegalArgumentException(
          "Missing value for required field `encryptionContext`"
        );
      }
      return new GetBranchKeyIdInput(this);
    }
  }
}
