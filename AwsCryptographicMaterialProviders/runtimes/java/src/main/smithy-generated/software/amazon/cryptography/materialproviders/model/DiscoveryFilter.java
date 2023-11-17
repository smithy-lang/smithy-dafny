// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.List;
import java.util.Objects;

/**
 * A filter which defines what AWS partition and AWS accounts a KMS Key may be in for a Keyring to be allowed to attempt to decrypt it.
 */
public class DiscoveryFilter {

  /**
   * A list of allowed AWS account IDs.
   */
  private final List<String> accountIds;

  /**
   * The AWS partition which is allowed.
   */
  private final String partition;

  protected DiscoveryFilter(BuilderImpl builder) {
    this.accountIds = builder.accountIds();
    this.partition = builder.partition();
  }

  /**
   * @return A list of allowed AWS account IDs.
   */
  public List<String> accountIds() {
    return this.accountIds;
  }

  /**
   * @return The AWS partition which is allowed.
   */
  public String partition() {
    return this.partition;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param accountIds A list of allowed AWS account IDs.
     */
    Builder accountIds(List<String> accountIds);

    /**
     * @return A list of allowed AWS account IDs.
     */
    List<String> accountIds();

    /**
     * @param partition The AWS partition which is allowed.
     */
    Builder partition(String partition);

    /**
     * @return The AWS partition which is allowed.
     */
    String partition();

    DiscoveryFilter build();
  }

  static class BuilderImpl implements Builder {

    protected List<String> accountIds;

    protected String partition;

    protected BuilderImpl() {}

    protected BuilderImpl(DiscoveryFilter model) {
      this.accountIds = model.accountIds();
      this.partition = model.partition();
    }

    public Builder accountIds(List<String> accountIds) {
      this.accountIds = accountIds;
      return this;
    }

    public List<String> accountIds() {
      return this.accountIds;
    }

    public Builder partition(String partition) {
      this.partition = partition;
      return this;
    }

    public String partition() {
      return this.partition;
    }

    public DiscoveryFilter build() {
      if (Objects.isNull(this.accountIds())) {
        throw new IllegalArgumentException(
          "Missing value for required field `accountIds`"
        );
      }
      if (Objects.isNull(this.partition())) {
        throw new IllegalArgumentException(
          "Missing value for required field `partition`"
        );
      }
      return new DiscoveryFilter(this);
    }
  }
}
