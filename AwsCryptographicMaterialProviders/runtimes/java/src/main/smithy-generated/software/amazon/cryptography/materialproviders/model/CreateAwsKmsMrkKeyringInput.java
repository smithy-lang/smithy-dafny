// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;

/**
 * Inputs for for creating an AWS KMS MRK Keyring.
 */
public class CreateAwsKmsMrkKeyringInput {

  /**
   * The identifier for the symmetric AWS KMS Key or AWS KMS Multi-Region Key responsible for wrapping and unwrapping data keys.
   */
  private final String kmsKeyId;

  /**
   * The KMS Client this Keyring will use to call KMS.
   */
  private final KmsClient kmsClient;

  /**
   * A list of grant tokens to be used when calling KMS.
   */
  private final List<String> grantTokens;

  protected CreateAwsKmsMrkKeyringInput(BuilderImpl builder) {
    this.kmsKeyId = builder.kmsKeyId();
    this.kmsClient = builder.kmsClient();
    this.grantTokens = builder.grantTokens();
  }

  /**
   * @return The identifier for the symmetric AWS KMS Key or AWS KMS Multi-Region Key responsible for wrapping and unwrapping data keys.
   */
  public String kmsKeyId() {
    return this.kmsKeyId;
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
     * @param kmsKeyId The identifier for the symmetric AWS KMS Key or AWS KMS Multi-Region Key responsible for wrapping and unwrapping data keys.
     */
    Builder kmsKeyId(String kmsKeyId);

    /**
     * @return The identifier for the symmetric AWS KMS Key or AWS KMS Multi-Region Key responsible for wrapping and unwrapping data keys.
     */
    String kmsKeyId();

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

    CreateAwsKmsMrkKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected String kmsKeyId;

    protected KmsClient kmsClient;

    protected List<String> grantTokens;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateAwsKmsMrkKeyringInput model) {
      this.kmsKeyId = model.kmsKeyId();
      this.kmsClient = model.kmsClient();
      this.grantTokens = model.grantTokens();
    }

    public Builder kmsKeyId(String kmsKeyId) {
      this.kmsKeyId = kmsKeyId;
      return this;
    }

    public String kmsKeyId() {
      return this.kmsKeyId;
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

    public CreateAwsKmsMrkKeyringInput build() {
      if (Objects.isNull(this.kmsKeyId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `kmsKeyId`"
        );
      }
      if (Objects.isNull(this.kmsClient())) {
        throw new IllegalArgumentException(
          "Missing value for required field `kmsClient`"
        );
      }
      return new CreateAwsKmsMrkKeyringInput(this);
    }
  }
}
