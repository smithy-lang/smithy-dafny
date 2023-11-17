// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.dynamodb.DynamoDbClient;
import software.amazon.awssdk.services.kms.KmsClient;

public class KeyStoreConfig {

  /**
   * The DynamoDB table name that backs this Key Store.
   */
  private final String ddbTableName;

  /**
   * The AWS KMS Key that protects this Key Store.
   */
  private final KMSConfiguration kmsConfiguration;

  /**
   * The logical name for this Key Store, which is cryptographically bound to the keys it holds.
   */
  private final String logicalKeyStoreName;

  /**
   * An identifier for this Key Store.
   */
  private final String id;

  /**
   * The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.
   */
  private final List<String> grantTokens;

  /**
   * The DynamoDB client this Key Store uses to call Amazon DynamoDB.
   */
  private final DynamoDbClient ddbClient;

  /**
   * The KMS client this Key Store uses to call AWS KMS.
   */
  private final KmsClient kmsClient;

  protected KeyStoreConfig(BuilderImpl builder) {
    this.ddbTableName = builder.ddbTableName();
    this.kmsConfiguration = builder.kmsConfiguration();
    this.logicalKeyStoreName = builder.logicalKeyStoreName();
    this.id = builder.id();
    this.grantTokens = builder.grantTokens();
    this.ddbClient = builder.ddbClient();
    this.kmsClient = builder.kmsClient();
  }

  /**
   * @return The DynamoDB table name that backs this Key Store.
   */
  public String ddbTableName() {
    return this.ddbTableName;
  }

  /**
   * @return The AWS KMS Key that protects this Key Store.
   */
  public KMSConfiguration kmsConfiguration() {
    return this.kmsConfiguration;
  }

  /**
   * @return The logical name for this Key Store, which is cryptographically bound to the keys it holds.
   */
  public String logicalKeyStoreName() {
    return this.logicalKeyStoreName;
  }

  /**
   * @return An identifier for this Key Store.
   */
  public String id() {
    return this.id;
  }

  /**
   * @return The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.
   */
  public List<String> grantTokens() {
    return this.grantTokens;
  }

  /**
   * @return The DynamoDB client this Key Store uses to call Amazon DynamoDB.
   */
  public DynamoDbClient ddbClient() {
    return this.ddbClient;
  }

  /**
   * @return The KMS client this Key Store uses to call AWS KMS.
   */
  public KmsClient kmsClient() {
    return this.kmsClient;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param ddbTableName The DynamoDB table name that backs this Key Store.
     */
    Builder ddbTableName(String ddbTableName);

    /**
     * @return The DynamoDB table name that backs this Key Store.
     */
    String ddbTableName();

    /**
     * @param kmsConfiguration The AWS KMS Key that protects this Key Store.
     */
    Builder kmsConfiguration(KMSConfiguration kmsConfiguration);

    /**
     * @return The AWS KMS Key that protects this Key Store.
     */
    KMSConfiguration kmsConfiguration();

    /**
     * @param logicalKeyStoreName The logical name for this Key Store, which is cryptographically bound to the keys it holds.
     */
    Builder logicalKeyStoreName(String logicalKeyStoreName);

    /**
     * @return The logical name for this Key Store, which is cryptographically bound to the keys it holds.
     */
    String logicalKeyStoreName();

    /**
     * @param id An identifier for this Key Store.
     */
    Builder id(String id);

    /**
     * @return An identifier for this Key Store.
     */
    String id();

    /**
     * @param grantTokens The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.
     */
    Builder grantTokens(List<String> grantTokens);

    /**
     * @return The AWS KMS grant tokens that are used when this Key Store calls to AWS KMS.
     */
    List<String> grantTokens();

    /**
     * @param ddbClient The DynamoDB client this Key Store uses to call Amazon DynamoDB.
     */
    Builder ddbClient(DynamoDbClient ddbClient);

    /**
     * @return The DynamoDB client this Key Store uses to call Amazon DynamoDB.
     */
    DynamoDbClient ddbClient();

    /**
     * @param kmsClient The KMS client this Key Store uses to call AWS KMS.
     */
    Builder kmsClient(KmsClient kmsClient);

    /**
     * @return The KMS client this Key Store uses to call AWS KMS.
     */
    KmsClient kmsClient();

    KeyStoreConfig build();
  }

  static class BuilderImpl implements Builder {

    protected String ddbTableName;

    protected KMSConfiguration kmsConfiguration;

    protected String logicalKeyStoreName;

    protected String id;

    protected List<String> grantTokens;

    protected DynamoDbClient ddbClient;

    protected KmsClient kmsClient;

    protected BuilderImpl() {}

    protected BuilderImpl(KeyStoreConfig model) {
      this.ddbTableName = model.ddbTableName();
      this.kmsConfiguration = model.kmsConfiguration();
      this.logicalKeyStoreName = model.logicalKeyStoreName();
      this.id = model.id();
      this.grantTokens = model.grantTokens();
      this.ddbClient = model.ddbClient();
      this.kmsClient = model.kmsClient();
    }

    public Builder ddbTableName(String ddbTableName) {
      this.ddbTableName = ddbTableName;
      return this;
    }

    public String ddbTableName() {
      return this.ddbTableName;
    }

    public Builder kmsConfiguration(KMSConfiguration kmsConfiguration) {
      this.kmsConfiguration = kmsConfiguration;
      return this;
    }

    public KMSConfiguration kmsConfiguration() {
      return this.kmsConfiguration;
    }

    public Builder logicalKeyStoreName(String logicalKeyStoreName) {
      this.logicalKeyStoreName = logicalKeyStoreName;
      return this;
    }

    public String logicalKeyStoreName() {
      return this.logicalKeyStoreName;
    }

    public Builder id(String id) {
      this.id = id;
      return this;
    }

    public String id() {
      return this.id;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public Builder ddbClient(DynamoDbClient ddbClient) {
      this.ddbClient = ddbClient;
      return this;
    }

    public DynamoDbClient ddbClient() {
      return this.ddbClient;
    }

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public KeyStoreConfig build() {
      if (Objects.isNull(this.ddbTableName())) {
        throw new IllegalArgumentException(
          "Missing value for required field `ddbTableName`"
        );
      }
      if (
        Objects.nonNull(this.ddbTableName()) && this.ddbTableName().length() < 3
      ) {
        throw new IllegalArgumentException(
          "The size of `ddbTableName` must be greater than or equal to 3"
        );
      }
      if (
        Objects.nonNull(this.ddbTableName()) &&
        this.ddbTableName().length() > 255
      ) {
        throw new IllegalArgumentException(
          "The size of `ddbTableName` must be less than or equal to 255"
        );
      }
      if (Objects.isNull(this.kmsConfiguration())) {
        throw new IllegalArgumentException(
          "Missing value for required field `kmsConfiguration`"
        );
      }
      if (Objects.isNull(this.logicalKeyStoreName())) {
        throw new IllegalArgumentException(
          "Missing value for required field `logicalKeyStoreName`"
        );
      }
      return new KeyStoreConfig(this);
    }
  }
}
