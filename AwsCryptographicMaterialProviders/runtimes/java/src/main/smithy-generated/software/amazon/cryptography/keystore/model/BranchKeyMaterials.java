// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.nio.ByteBuffer;
import java.util.Map;
import java.util.Objects;

public class BranchKeyMaterials {

  private final String branchKeyIdentifier;

  private final String branchKeyVersion;

  private final Map<String, String> encryptionContext;

  private final ByteBuffer branchKey;

  protected BranchKeyMaterials(BuilderImpl builder) {
    this.branchKeyIdentifier = builder.branchKeyIdentifier();
    this.branchKeyVersion = builder.branchKeyVersion();
    this.encryptionContext = builder.encryptionContext();
    this.branchKey = builder.branchKey();
  }

  public String branchKeyIdentifier() {
    return this.branchKeyIdentifier;
  }

  public String branchKeyVersion() {
    return this.branchKeyVersion;
  }

  public Map<String, String> encryptionContext() {
    return this.encryptionContext;
  }

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
    Builder branchKeyIdentifier(String branchKeyIdentifier);

    String branchKeyIdentifier();

    Builder branchKeyVersion(String branchKeyVersion);

    String branchKeyVersion();

    Builder encryptionContext(Map<String, String> encryptionContext);

    Map<String, String> encryptionContext();

    Builder branchKey(ByteBuffer branchKey);

    ByteBuffer branchKey();

    BranchKeyMaterials build();
  }

  static class BuilderImpl implements Builder {

    protected String branchKeyIdentifier;

    protected String branchKeyVersion;

    protected Map<String, String> encryptionContext;

    protected ByteBuffer branchKey;

    protected BuilderImpl() {}

    protected BuilderImpl(BranchKeyMaterials model) {
      this.branchKeyIdentifier = model.branchKeyIdentifier();
      this.branchKeyVersion = model.branchKeyVersion();
      this.encryptionContext = model.encryptionContext();
      this.branchKey = model.branchKey();
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

    public Builder encryptionContext(Map<String, String> encryptionContext) {
      this.encryptionContext = encryptionContext;
      return this;
    }

    public Map<String, String> encryptionContext() {
      return this.encryptionContext;
    }

    public Builder branchKey(ByteBuffer branchKey) {
      this.branchKey = branchKey;
      return this;
    }

    public ByteBuffer branchKey() {
      return this.branchKey;
    }

    public BranchKeyMaterials build() {
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
      if (Objects.isNull(this.encryptionContext())) {
        throw new IllegalArgumentException(
          "Missing value for required field `encryptionContext`"
        );
      }
      if (Objects.isNull(this.branchKey())) {
        throw new IllegalArgumentException(
          "Missing value for required field `branchKey`"
        );
      }
      return new BranchKeyMaterials(this);
    }
  }
}
