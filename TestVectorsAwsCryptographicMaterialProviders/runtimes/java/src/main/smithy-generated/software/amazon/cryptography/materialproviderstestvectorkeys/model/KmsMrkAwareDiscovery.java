// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;
import software.amazon.cryptography.materialproviders.model.DiscoveryFilter;

public class KmsMrkAwareDiscovery {

  private final String keyId;

  private final String defaultMrkRegion;

  /**
   * A filter which defines what AWS partition and AWS accounts a KMS Key may be in for a Keyring to be allowed to attempt to decrypt it.
   */
  private final DiscoveryFilter awsKmsDiscoveryFilter;

  protected KmsMrkAwareDiscovery(BuilderImpl builder) {
    this.keyId = builder.keyId();
    this.defaultMrkRegion = builder.defaultMrkRegion();
    this.awsKmsDiscoveryFilter = builder.awsKmsDiscoveryFilter();
  }

  public String keyId() {
    return this.keyId;
  }

  public String defaultMrkRegion() {
    return this.defaultMrkRegion;
  }

  /**
   * @return A filter which defines what AWS partition and AWS accounts a KMS Key may be in for a Keyring to be allowed to attempt to decrypt it.
   */
  public DiscoveryFilter awsKmsDiscoveryFilter() {
    return this.awsKmsDiscoveryFilter;
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

    Builder defaultMrkRegion(String defaultMrkRegion);

    String defaultMrkRegion();

    /**
     * @param awsKmsDiscoveryFilter A filter which defines what AWS partition and AWS accounts a KMS Key may be in for a Keyring to be allowed to attempt to decrypt it.
     */
    Builder awsKmsDiscoveryFilter(DiscoveryFilter awsKmsDiscoveryFilter);

    /**
     * @return A filter which defines what AWS partition and AWS accounts a KMS Key may be in for a Keyring to be allowed to attempt to decrypt it.
     */
    DiscoveryFilter awsKmsDiscoveryFilter();

    KmsMrkAwareDiscovery build();
  }

  static class BuilderImpl implements Builder {

    protected String keyId;

    protected String defaultMrkRegion;

    protected DiscoveryFilter awsKmsDiscoveryFilter;

    protected BuilderImpl() {}

    protected BuilderImpl(KmsMrkAwareDiscovery model) {
      this.keyId = model.keyId();
      this.defaultMrkRegion = model.defaultMrkRegion();
      this.awsKmsDiscoveryFilter = model.awsKmsDiscoveryFilter();
    }

    public Builder keyId(String keyId) {
      this.keyId = keyId;
      return this;
    }

    public String keyId() {
      return this.keyId;
    }

    public Builder defaultMrkRegion(String defaultMrkRegion) {
      this.defaultMrkRegion = defaultMrkRegion;
      return this;
    }

    public String defaultMrkRegion() {
      return this.defaultMrkRegion;
    }

    public Builder awsKmsDiscoveryFilter(
      DiscoveryFilter awsKmsDiscoveryFilter
    ) {
      this.awsKmsDiscoveryFilter = awsKmsDiscoveryFilter;
      return this;
    }

    public DiscoveryFilter awsKmsDiscoveryFilter() {
      return this.awsKmsDiscoveryFilter;
    }

    public KmsMrkAwareDiscovery build() {
      if (Objects.isNull(this.keyId())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyId`"
        );
      }
      if (Objects.isNull(this.defaultMrkRegion())) {
        throw new IllegalArgumentException(
          "Missing value for required field `defaultMrkRegion`"
        );
      }
      return new KmsMrkAwareDiscovery(this);
    }
  }
}
