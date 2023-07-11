// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;
import software.amazon.cryptography.keystore.KeyStore;
import software.amazon.cryptography.materialproviders.BranchKeyIdSupplier;
import software.amazon.cryptography.materialproviders.IBranchKeyIdSupplier;

/**
 * Inputs for creating a Hierarchical Keyring.
 */
public class CreateAwsKmsHierarchicalKeyringInput {
  /**
   * The identifier for the single Branch Key responsible for wrapping and unwrapping the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
   */
  private final String branchKeyId;

  /**
   * A Branch Key Supplier which determines what Branch Key to use to wrap and unwrap the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
   */
  private final IBranchKeyIdSupplier branchKeyIdSupplier;

  /**
   * The Key Store which contains the Branch Key(s) responsible for wrapping and unwrapping data keys.
   */
  private final KeyStore keyStore;

  /**
   * How many seconds the Branch Key material is allowed to be reused within the local cache before it is re-retrieved from Amazon DynamoDB and re-authenticated with AWS KMS.
   */
  private final long ttlSeconds;

  /**
   * How many entries the local cache for Branch Key material can hold before evicting older entries.
   */
  private final int maxCacheSize;

  /**
   * Fine tune material refresh settings.
   */
  private final StormTrackerSettings trackerSettings;

  protected CreateAwsKmsHierarchicalKeyringInput(BuilderImpl builder) {
    this.branchKeyId = builder.branchKeyId();
    this.branchKeyIdSupplier = builder.branchKeyIdSupplier();
    this.keyStore = builder.keyStore();
    this.ttlSeconds = builder.ttlSeconds();
    this.maxCacheSize = builder.maxCacheSize();
    this.trackerSettings = builder.trackerSettings();
  }

  /**
   * @return The identifier for the single Branch Key responsible for wrapping and unwrapping the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
   */
  public String branchKeyId() {
    return this.branchKeyId;
  }

  /**
   * @return A Branch Key Supplier which determines what Branch Key to use to wrap and unwrap the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
   */
  public IBranchKeyIdSupplier branchKeyIdSupplier() {
    return this.branchKeyIdSupplier;
  }

  /**
   * @return The Key Store which contains the Branch Key(s) responsible for wrapping and unwrapping data keys.
   */
  public KeyStore keyStore() {
    return this.keyStore;
  }

  /**
   * @return How many seconds the Branch Key material is allowed to be reused within the local cache before it is re-retrieved from Amazon DynamoDB and re-authenticated with AWS KMS.
   */
  public long ttlSeconds() {
    return this.ttlSeconds;
  }

  /**
   * @return How many entries the local cache for Branch Key material can hold before evicting older entries.
   */
  public int maxCacheSize() {
    return this.maxCacheSize;
  }

  /**
   * @return Fine tune material refresh settings.
   */
  public StormTrackerSettings trackerSettings() {
    return this.trackerSettings;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param branchKeyId The identifier for the single Branch Key responsible for wrapping and unwrapping the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
     */
    Builder branchKeyId(String branchKeyId);

    /**
     * @return The identifier for the single Branch Key responsible for wrapping and unwrapping the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
     */
    String branchKeyId();

    /**
     * @param branchKeyIdSupplier A Branch Key Supplier which determines what Branch Key to use to wrap and unwrap the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
     */
    Builder branchKeyIdSupplier(IBranchKeyIdSupplier branchKeyIdSupplier);

    /**
     * @return A Branch Key Supplier which determines what Branch Key to use to wrap and unwrap the data key. Either a Branch Key ID or Branch Key Supplier must be specified.
     */
    IBranchKeyIdSupplier branchKeyIdSupplier();

    /**
     * @param keyStore The Key Store which contains the Branch Key(s) responsible for wrapping and unwrapping data keys.
     */
    Builder keyStore(KeyStore keyStore);

    /**
     * @return The Key Store which contains the Branch Key(s) responsible for wrapping and unwrapping data keys.
     */
    KeyStore keyStore();

    /**
     * @param ttlSeconds How many seconds the Branch Key material is allowed to be reused within the local cache before it is re-retrieved from Amazon DynamoDB and re-authenticated with AWS KMS.
     */
    Builder ttlSeconds(long ttlSeconds);

    /**
     * @return How many seconds the Branch Key material is allowed to be reused within the local cache before it is re-retrieved from Amazon DynamoDB and re-authenticated with AWS KMS.
     */
    long ttlSeconds();

    /**
     * @param maxCacheSize How many entries the local cache for Branch Key material can hold before evicting older entries.
     */
    Builder maxCacheSize(int maxCacheSize);

    /**
     * @return How many entries the local cache for Branch Key material can hold before evicting older entries.
     */
    int maxCacheSize();

    /**
     * @param trackerSettings Fine tune material refresh settings.
     */
    Builder trackerSettings(StormTrackerSettings trackerSettings);

    /**
     * @return Fine tune material refresh settings.
     */
    StormTrackerSettings trackerSettings();

    CreateAwsKmsHierarchicalKeyringInput build();
  }

  static class BuilderImpl implements Builder {
    protected String branchKeyId;

    protected IBranchKeyIdSupplier branchKeyIdSupplier;

    protected KeyStore keyStore;

    protected long ttlSeconds;

    private boolean _ttlSecondsSet = false;

    protected int maxCacheSize;

    private boolean _maxCacheSizeSet = false;

    protected StormTrackerSettings trackerSettings;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateAwsKmsHierarchicalKeyringInput model) {
      this.branchKeyId = model.branchKeyId();
      this.branchKeyIdSupplier = model.branchKeyIdSupplier();
      this.keyStore = model.keyStore();
      this.ttlSeconds = model.ttlSeconds();
      this._ttlSecondsSet = true;
      this.maxCacheSize = model.maxCacheSize();
      this._maxCacheSizeSet = true;
      this.trackerSettings = model.trackerSettings();
    }

    public Builder branchKeyId(String branchKeyId) {
      this.branchKeyId = branchKeyId;
      return this;
    }

    public String branchKeyId() {
      return this.branchKeyId;
    }

    public Builder branchKeyIdSupplier(IBranchKeyIdSupplier branchKeyIdSupplier) {
      this.branchKeyIdSupplier = BranchKeyIdSupplier.wrap(branchKeyIdSupplier);
      return this;
    }

    public IBranchKeyIdSupplier branchKeyIdSupplier() {
      return this.branchKeyIdSupplier;
    }

    public Builder keyStore(KeyStore keyStore) {
      this.keyStore = keyStore;
      return this;
    }

    public KeyStore keyStore() {
      return this.keyStore;
    }

    public Builder ttlSeconds(long ttlSeconds) {
      this.ttlSeconds = ttlSeconds;
      this._ttlSecondsSet = true;
      return this;
    }

    public long ttlSeconds() {
      return this.ttlSeconds;
    }

    public Builder maxCacheSize(int maxCacheSize) {
      this.maxCacheSize = maxCacheSize;
      this._maxCacheSizeSet = true;
      return this;
    }

    public int maxCacheSize() {
      return this.maxCacheSize;
    }

    public Builder trackerSettings(StormTrackerSettings trackerSettings) {
      this.trackerSettings = trackerSettings;
      return this;
    }

    public StormTrackerSettings trackerSettings() {
      return this.trackerSettings;
    }

    public CreateAwsKmsHierarchicalKeyringInput build() {
      if (Objects.isNull(this.keyStore()))  {
        throw new IllegalArgumentException("Missing value for required field `keyStore`");
      }
      if (!this._ttlSecondsSet) {
        throw new IllegalArgumentException("Missing value for required field `ttlSeconds`");
      }
      if (this._ttlSecondsSet && this.ttlSeconds() < 0) {
        throw new IllegalArgumentException("`ttlSeconds` must be greater than or equal to 0");
      }
      if (this._maxCacheSizeSet && this.maxCacheSize() < 0) {
        throw new IllegalArgumentException("`maxCacheSize` must be greater than or equal to 0");
      }
      return new CreateAwsKmsHierarchicalKeyringInput(this);
    }
  }
}
