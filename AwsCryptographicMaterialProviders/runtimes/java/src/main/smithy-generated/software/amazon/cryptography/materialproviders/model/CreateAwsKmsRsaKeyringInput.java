// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.nio.ByteBuffer;
import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;
import software.amazon.awssdk.services.kms.model.EncryptionAlgorithmSpec;

/**
 * Inputs for creating a AWS KMS RSA Keyring.
 */
public class CreateAwsKmsRsaKeyringInput {

  /**
   * The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. This should be the public key as exported from KMS. If not specified, this Keyring cannot be used on encrypt.
   */
  private final ByteBuffer publicKey;

  /**
   * The ARN for the asymmetric AWS KMS Key for RSA responsible for wrapping and unwrapping data keys.
   */
  private final String kmsKeyId;

  /**
   * The RSA algorithm used to wrap and unwrap data keys.
   */
  private final EncryptionAlgorithmSpec encryptionAlgorithm;

  /**
   * The KMS Client this Keyring will use to call KMS.
   */
  private final KmsClient kmsClient;

  /**
   * A list of grant tokens to be used when calling KMS.
   */
  private final List<String> grantTokens;

  protected CreateAwsKmsRsaKeyringInput(BuilderImpl builder) {
    this.publicKey = builder.publicKey();
    this.kmsKeyId = builder.kmsKeyId();
    this.encryptionAlgorithm = builder.encryptionAlgorithm();
    this.kmsClient = builder.kmsClient();
    this.grantTokens = builder.grantTokens();
  }

  /**
   * @return The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. This should be the public key as exported from KMS. If not specified, this Keyring cannot be used on encrypt.
   */
  public ByteBuffer publicKey() {
    return this.publicKey;
  }

  /**
   * @return The ARN for the asymmetric AWS KMS Key for RSA responsible for wrapping and unwrapping data keys.
   */
  public String kmsKeyId() {
    return this.kmsKeyId;
  }

  /**
   * @return The RSA algorithm used to wrap and unwrap data keys.
   */
  public EncryptionAlgorithmSpec encryptionAlgorithm() {
    return this.encryptionAlgorithm;
  }

  /**
   * @return The KMS Client this Keyring will use to call KMS.
   */
  public KmsClient kmsClient() {
    return this.kmsClient;
  }

  /**
   * @return A list of grant tokens to be used when calling KMS.
   */
  public List<String> grantTokens() {
    return this.grantTokens;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param publicKey The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. This should be the public key as exported from KMS. If not specified, this Keyring cannot be used on encrypt.
     */
    Builder publicKey(ByteBuffer publicKey);

    /**
     * @return The public RSA Key responsible for wrapping data keys, as a UTF8 encoded, PEM encoded X.509 SubjectPublicKeyInfo structure. This should be the public key as exported from KMS. If not specified, this Keyring cannot be used on encrypt.
     */
    ByteBuffer publicKey();

    /**
     * @param kmsKeyId The ARN for the asymmetric AWS KMS Key for RSA responsible for wrapping and unwrapping data keys.
     */
    Builder kmsKeyId(String kmsKeyId);

    /**
     * @return The ARN for the asymmetric AWS KMS Key for RSA responsible for wrapping and unwrapping data keys.
     */
    String kmsKeyId();

    /**
     * @param encryptionAlgorithm The RSA algorithm used to wrap and unwrap data keys.
     */
    Builder encryptionAlgorithm(EncryptionAlgorithmSpec encryptionAlgorithm);

    /**
     * @return The RSA algorithm used to wrap and unwrap data keys.
     */
    EncryptionAlgorithmSpec encryptionAlgorithm();

    /**
     * @param kmsClient The KMS Client this Keyring will use to call KMS.
     */
    Builder kmsClient(KmsClient kmsClient);

    /**
     * @return The KMS Client this Keyring will use to call KMS.
     */
    KmsClient kmsClient();

    /**
     * @param grantTokens A list of grant tokens to be used when calling KMS.
     */
    Builder grantTokens(List<String> grantTokens);

    /**
     * @return A list of grant tokens to be used when calling KMS.
     */
    List<String> grantTokens();

    CreateAwsKmsRsaKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected ByteBuffer publicKey;

    protected String kmsKeyId;

    protected EncryptionAlgorithmSpec encryptionAlgorithm;

    protected KmsClient kmsClient;

    protected List<String> grantTokens;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateAwsKmsRsaKeyringInput model) {
      this.publicKey = model.publicKey();
      this.kmsKeyId = model.kmsKeyId();
      this.encryptionAlgorithm = model.encryptionAlgorithm();
      this.kmsClient = model.kmsClient();
      this.grantTokens = model.grantTokens();
    }

    public Builder publicKey(ByteBuffer publicKey) {
      this.publicKey = publicKey;
      return this;
    }

    public ByteBuffer publicKey() {
      return this.publicKey;
    }

    public Builder kmsKeyId(String kmsKeyId) {
      this.kmsKeyId = kmsKeyId;
      return this;
    }

    public String kmsKeyId() {
      return this.kmsKeyId;
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

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsRsaKeyringInput build() {
      if (Objects.isNull(this.kmsKeyId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `kmsKeyId`"
        );
      }
      if (Objects.isNull(this.encryptionAlgorithm())) {
        throw new IllegalArgumentException(
          "Missing value for required field `encryptionAlgorithm`"
        );
      }
      return new CreateAwsKmsRsaKeyringInput(this);
    }
  }
}
