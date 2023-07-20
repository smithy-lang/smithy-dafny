// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Map;

public class CreateKeyInput {
  /**
   * The identifier for the created Branch Key.
   */
  private final String branchKeyIdentifier;

  /**
   * Custom encryption context for the Branch Key.
   */
  private final Map<String, String> encryptionContext;

  protected CreateKeyInput(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.encryptionContext = builder.encryptionContext();
  }

  /**
   * @return The identifier for the created Branch Key.
   */
  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  /**
   * @return Custom encryption context for the Branch Key.
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
     * @param branchKeyIdentifier The identifier for the created Branch Key.
     */
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    /**
     * @return The identifier for the created Branch Key.
     */
    String branchKeyIdentifier();

    /**
     * @param encryptionContext Custom encryption context for the Branch Key.
     */
    Builder encryptionContext(Map<String, String> encryptionContext);

    /**
     * @return Custom encryption context for the Branch Key.
     */
    Map<String, String> encryptionContext();

    CreateKeyInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyIdentifier;

    protected Map<String, String> encryptionContext;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateKeyInput model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.encryptionContext = model.encryptionContext();
    }

    public Builder branchKeyIdentifier(String branchKeyIdentifier) {
      this.branchKeyIdentifier = branchKeyIdentifier;
      return this;
    }

    public String branchKeyIdentifier() {
      return this.branchKeyIdentifier;
    }

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public CreateKeyInput build() {
      return new CreateKeyInput(this);
    }
  }
}
