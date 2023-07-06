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
   * How many seconds before expiration should an attempt be made to refresh the materials.
   */
  private final int gracePeriod;

  /**
   * How many seconds between attempts to refresh the materials.
   */
  private final int graceInterval;

  /**
   * How many simultaneous attempts to refresh the materials.
   */
  private final int fanOut;

  /**
   * How many seconds until an attempt to refresh the materials should be forgotten.
   */
  private final int inFlightTTL;

  protected CreateAwsKmsHierarchicalKeyringInput(BuilderImpl builder) {
    this.branchKeyId = builder.branchKeyId();
    this.branchKeyIdSupplier = builder.branchKeyIdSupplier();
    this.keyStore = builder.keyStore();
    this.ttlSeconds = builder.ttlSeconds();
    this.maxCacheSize = builder.maxCacheSize();
    this.gracePeriod = builder.gracePeriod();
    this.graceInterval = builder.graceInterval();
    this.fanOut = builder.fanOut();
    this.inFlightTTL = builder.inFlightTTL();
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
   * @return How many seconds before expiration should an attempt be made to refresh the materials.
   */
  public int gracePeriod() {
    return this.gracePeriod;
  }

  /**
   * @return How many seconds between attempts to refresh the materials.
   */
  public int graceInterval() {
    return this.graceInterval;
  }

  /**
   * @return How many simultaneous attempts to refresh the materials.
   */
  public int fanOut() {
    return this.fanOut;
  }

  /**
   * @return How many seconds until an attempt to refresh the materials should be forgotten.
   */
  public int inFlightTTL() {
    return this.inFlightTTL;
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
     * @param gracePeriod How many seconds before expiration should an attempt be made to refresh the materials.
     */
    Builder gracePeriod(int gracePeriod);

    /**
     * @return How many seconds before expiration should an attempt be made to refresh the materials.
     */
    int gracePeriod();

    /**
     * @param graceInterval How many seconds between attempts to refresh the materials.
     */
    Builder graceInterval(int graceInterval);

    /**
     * @return How many seconds between attempts to refresh the materials.
     */
    int graceInterval();

    /**
     * @param fanOut How many simultaneous attempts to refresh the materials.
     */
    Builder fanOut(int fanOut);

    /**
     * @return How many simultaneous attempts to refresh the materials.
     */
    int fanOut();

    /**
     * @param inFlightTTL How many seconds until an attempt to refresh the materials should be forgotten.
     */
    Builder inFlightTTL(int inFlightTTL);

    /**
     * @return How many seconds until an attempt to refresh the materials should be forgotten.
     */
    int inFlightTTL();

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

    protected int gracePeriod;

    private boolean _gracePeriodSet = false;

    protected int graceInterval;

    private boolean _graceIntervalSet = false;

    protected int fanOut;

    private boolean _fanOutSet = false;

    protected int inFlightTTL;

    private boolean _inFlightTTLSet = false;

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
      this.gracePeriod = model.gracePeriod();
      this._gracePeriodSet = true;
      this.graceInterval = model.graceInterval();
      this._graceIntervalSet = true;
      this.fanOut = model.fanOut();
      this._fanOutSet = true;
      this.inFlightTTL = model.inFlightTTL();
      this._inFlightTTLSet = true;
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

    public Builder gracePeriod(int gracePeriod) {
      this.gracePeriod = gracePeriod;
      this._gracePeriodSet = true;
      return this;
    }

    public int gracePeriod() {
      return this.gracePeriod;
    }

    public Builder graceInterval(int graceInterval) {
      this.graceInterval = graceInterval;
      this._graceIntervalSet = true;
      return this;
    }

    public int graceInterval() {
      return this.graceInterval;
    }

    public Builder fanOut(int fanOut) {
      this.fanOut = fanOut;
      this._fanOutSet = true;
      return this;
    }

    public int fanOut() {
      return this.fanOut;
    }

    public Builder inFlightTTL(int inFlightTTL) {
      this.inFlightTTL = inFlightTTL;
      this._inFlightTTLSet = true;
      return this;
    }

    public int inFlightTTL() {
      return this.inFlightTTL;
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
      if (this._gracePeriodSet && this.gracePeriod() < 0) {
        throw new IllegalArgumentException("`gracePeriod` must be greater than or equal to 0");
      }
      if (this._graceIntervalSet && this.graceInterval() < 0) {
        throw new IllegalArgumentException("`graceInterval` must be greater than or equal to 0");
      }
      if (this._fanOutSet && this.fanOut() < 0) {
        throw new IllegalArgumentException("`fanOut` must be greater than or equal to 0");
      }
      if (this._inFlightTTLSet && this.inFlightTTL() < 0) {
        throw new IllegalArgumentException("`inFlightTTL` must be greater than or equal to 0");
      }
      return new CreateAwsKmsHierarchicalKeyringInput(this);
    }
  }
}
