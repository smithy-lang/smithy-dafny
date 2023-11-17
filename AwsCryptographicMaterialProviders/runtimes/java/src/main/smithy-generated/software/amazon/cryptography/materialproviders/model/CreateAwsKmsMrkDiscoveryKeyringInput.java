// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.awssdk.services.kms.KmsClient;

/**
 * Inputs for for creating a AWS KMS MRK Discovery Keyring.
 */
public class CreateAwsKmsMrkDiscoveryKeyringInput {

  /**
   * The KMS Client this Keyring will use to call KMS.
   */
  private final KmsClient kmsClient;

  /**
   * A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
   */
  private final DiscoveryFilter discoveryFilter;

  /**
   * A list of grant tokens to be used when calling KMS.
   */
  private final List<String> grantTokens;

  /**
   * The region the input 'kmsClient' is in.
   */
  private final String region;

  protected CreateAwsKmsMrkDiscoveryKeyringInput(BuilderImpl builder) {
    this.kmsClient = builder.kmsClient();
    this.discoveryFilter = builder.discoveryFilter();
    this.grantTokens = builder.grantTokens();
    this.region = builder.region();
  }

  /**
   * @return The KMS Client this Keyring will use to call KMS.
   */
  public KmsClient kmsClient() {
    return this.kmsClient;
  }

  /**
   * @return A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
   */
  public DiscoveryFilter discoveryFilter() {
    return this.discoveryFilter;
  }

  /**
   * @return A list of grant tokens to be used when calling KMS.
   */
  public List<String> grantTokens() {
    return this.grantTokens;
  }

  /**
   * @return The region the input 'kmsClient' is in.
   */
  public String region() {
    return this.region;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param kmsClient The KMS Client this Keyring will use to call KMS.
     */
    Builder kmsClient(KmsClient kmsClient);

    /**
     * @return The KMS Client this Keyring will use to call KMS.
     */
    KmsClient kmsClient();

    /**
     * @param discoveryFilter A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
     */
    Builder discoveryFilter(DiscoveryFilter discoveryFilter);

    /**
     * @return A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
     */
    DiscoveryFilter discoveryFilter();

    /**
     * @param grantTokens A list of grant tokens to be used when calling KMS.
     */
    Builder grantTokens(List<String> grantTokens);

    /**
     * @return A list of grant tokens to be used when calling KMS.
     */
    List<String> grantTokens();

    /**
     * @param region The region the input 'kmsClient' is in.
     */
    Builder region(String region);

    /**
     * @return The region the input 'kmsClient' is in.
     */
    String region();

    CreateAwsKmsMrkDiscoveryKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected KmsClient kmsClient;

    protected DiscoveryFilter discoveryFilter;

    protected List<String> grantTokens;

    protected String region;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateAwsKmsMrkDiscoveryKeyringInput model) {
      this.kmsClient = model.kmsClient();
      this.discoveryFilter = model.discoveryFilter();
      this.grantTokens = model.grantTokens();
      this.region = model.region();
    }

    public Builder kmsClient(KmsClient kmsClient) {
      this.kmsClient = kmsClient;
      return this;
    }

    public KmsClient kmsClient() {
      return this.kmsClient;
    }

    public Builder discoveryFilter(DiscoveryFilter discoveryFilter) {
      this.discoveryFilter = discoveryFilter;
      return this;
    }

    public DiscoveryFilter discoveryFilter() {
      return this.discoveryFilter;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public Builder region(String region) {
      this.region = region;
      return this;
    }

    public String region() {
      return this.region;
    }

    public CreateAwsKmsMrkDiscoveryKeyringInput build() {
      if (Objects.isNull(this.kmsClient())) {
        throw new IllegalArgumentException(
          "Missing value for required field `kmsClient`"
        );
      }
      if (Objects.isNull(this.region())) {
        throw new IllegalArgumentException(
          "Missing value for required field `region`"
        );
      }
      return new CreateAwsKmsMrkDiscoveryKeyringInput(this);
    }
  }
}
