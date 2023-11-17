// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;
import software.amazon.awssdk.services.kms.model.EncryptionAlgorithmSpec;

public class KmsRsaKeyring {

  private final String keyId;

  private final EncryptionAlgorithmSpec encryptionAlgorithm;

  protected KmsRsaKeyring(BuilderImpl builder) {
    this.keyId = builder.keyId();
    this.encryptionAlgorithm = builder.encryptionAlgorithm();
  }

  public String keyId() {
    return this.keyId;
  }

  public EncryptionAlgorithmSpec encryptionAlgorithm() {
    return this.encryptionAlgorithm;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyId(String keyId);

    String keyId();

    Builder encryptionAlgorithm(EncryptionAlgorithmSpec encryptionAlgorithm);

    EncryptionAlgorithmSpec encryptionAlgorithm();

    KmsRsaKeyring build();
  }

  static class BuilderImpl implements Builder {

    protected String keyId;

    protected EncryptionAlgorithmSpec encryptionAlgorithm;

    protected BuilderImpl() {}

    protected BuilderImpl(KmsRsaKeyring model) {
      this.keyId = model.keyId();
      this.encryptionAlgorithm = model.encryptionAlgorithm();
    }

    public Builder keyId(String keyId) {
      this.keyId = keyId;
      return this;
    }

    public String keyId() {
      return this.keyId;
    }

    public Builder encryptionAlgorithm(
      EncryptionAlgorithmSpec encryptionAlgorithm
    ) {
      this.encryptionAlgorithm = encryptionAlgorithm;
      return this;
    }

    public EncryptionAlgorithmSpec encryptionAlgorithm() {
      return this.encryptionAlgorithm;
    }

    public KmsRsaKeyring build() {
      if (Objects.isNull(this.keyId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyId`"
        );
      }
      if (Objects.isNull(this.encryptionAlgorithm())) {
        throw new IllegalArgumentException(
          "Missing value for required field `encryptionAlgorithm`"
        );
      }
      return new KmsRsaKeyring(this);
    }
  }
}
