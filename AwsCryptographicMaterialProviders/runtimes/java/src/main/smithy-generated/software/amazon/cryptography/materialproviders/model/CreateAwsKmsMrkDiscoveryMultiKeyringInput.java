// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;
import software.amazon.cryptography.materialproviders.ClientSupplier;
import software.amazon.cryptography.materialproviders.IClientSupplier;

/**
 * Inputs for for creating a AWS KMS MRK Discovery Multi-Keyring.
 */
public class CreateAwsKmsMrkDiscoveryMultiKeyringInput {

  /**
   * The list of regions this Keyring will creates KMS clients for.
   */
  private final List<String> regions;

  /**
   * A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
   */
  private final DiscoveryFilter discoveryFilter;

  /**
   * The Client Supplier which will be used to get KMS Clients for use with this Keyring. If not specified on input, a Default Client Supplier is created which creates a KMS Client for each region in the 'regions' input.
   */
  private final IClientSupplier clientSupplier;

  /**
   * A list of grant tokens to be used when calling KMS.
   */
  private final List<String> grantTokens;

  protected CreateAwsKmsMrkDiscoveryMultiKeyringInput(BuilderImpl builder) {
    this.regions = builder.regions();
    this.discoveryFilter = builder.discoveryFilter();
    this.clientSupplier = builder.clientSupplier();
    this.grantTokens = builder.grantTokens();
  }

  /**
   * @return The list of regions this Keyring will creates KMS clients for.
   */
  public List<String> regions() {
    return this.regions;
  }

  /**
   * @return A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
   */
  public DiscoveryFilter discoveryFilter() {
    return this.discoveryFilter;
  }

  /**
   * @return The Client Supplier which will be used to get KMS Clients for use with this Keyring. If not specified on input, a Default Client Supplier is created which creates a KMS Client for each region in the 'regions' input.
   */
  public IClientSupplier clientSupplier() {
    return this.clientSupplier;
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
     * @param regions The list of regions this Keyring will creates KMS clients for.
     */
    Builder regions(List<String> regions);

    /**
     * @return The list of regions this Keyring will creates KMS clients for.
     */
    List<String> regions();

    /**
     * @param discoveryFilter A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
     */
    Builder discoveryFilter(DiscoveryFilter discoveryFilter);

    /**
     * @return A filter which restricts which KMS Keys this Keyring may attempt to decrypt with by AWS partition and account.
     */
    DiscoveryFilter discoveryFilter();

    /**
     * @param clientSupplier The Client Supplier which will be used to get KMS Clients for use with this Keyring. If not specified on input, a Default Client Supplier is created which creates a KMS Client for each region in the 'regions' input.
     */
    Builder clientSupplier(IClientSupplier clientSupplier);

    /**
     * @return The Client Supplier which will be used to get KMS Clients for use with this Keyring. If not specified on input, a Default Client Supplier is created which creates a KMS Client for each region in the 'regions' input.
     */
    IClientSupplier clientSupplier();

    /**
     * @param grantTokens A list of grant tokens to be used when calling KMS.
     */
    Builder grantTokens(List<String> grantTokens);

    /**
     * @return A list of grant tokens to be used when calling KMS.
     */
    List<String> grantTokens();

    CreateAwsKmsMrkDiscoveryMultiKeyringInput build();
  }

  static class BuilderImpl implements Builder {

    protected List<String> regions;

    protected DiscoveryFilter discoveryFilter;

    protected IClientSupplier clientSupplier;

    protected List<String> grantTokens;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateAwsKmsMrkDiscoveryMultiKeyringInput model) {
      this.regions = model.regions();
      this.discoveryFilter = model.discoveryFilter();
      this.clientSupplier = model.clientSupplier();
      this.grantTokens = model.grantTokens();
    }

    public Builder regions(List<String> regions) {
      this.regions = regions;
      return this;
    }

    public List<String> regions() {
      return this.regions;
    }

    public Builder discoveryFilter(DiscoveryFilter discoveryFilter) {
      this.discoveryFilter = discoveryFilter;
      return this;
    }

    public DiscoveryFilter discoveryFilter() {
      return this.discoveryFilter;
    }

    public Builder clientSupplier(IClientSupplier clientSupplier) {
      this.clientSupplier = ClientSupplier.wrap(clientSupplier);
      return this;
    }

    public IClientSupplier clientSupplier() {
      return this.clientSupplier;
    }

    public Builder grantTokens(List<String> grantTokens) {
      this.grantTokens = grantTokens;
      return this;
    }

    public List<String> grantTokens() {
      return this.grantTokens;
    }

    public CreateAwsKmsMrkDiscoveryMultiKeyringInput build() {
      if (Objects.isNull(this.regions())) {
        throw new IllegalArgumentException(
          "Missing value for required field `regions`"
        );
      }
      return new CreateAwsKmsMrkDiscoveryMultiKeyringInput(this);
    }
  }
}
