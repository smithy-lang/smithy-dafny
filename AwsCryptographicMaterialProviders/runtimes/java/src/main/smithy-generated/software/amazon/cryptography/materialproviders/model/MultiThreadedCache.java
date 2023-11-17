// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

/**
 * A cache that is safe for use in a multi threaded environment, but no extra functionality.
 */
public class MultiThreadedCache {

  /**
   * Maximum number of entries cached.
   */
  private final int entryCapacity;

  /**
   * Number of entries to prune at a time.
   */
  private final int entryPruningTailSize;

  protected MultiThreadedCache(BuilderImpl builder) {
    this.entryCapacity = builder.entryCapacity();
    this.entryPruningTailSize = builder.entryPruningTailSize();
  }

  /**
   * @return Maximum number of entries cached.
   */
  public int entryCapacity() {
    return this.entryCapacity;
  }

  /**
   * @return Number of entries to prune at a time.
   */
  public int entryPruningTailSize() {
    return this.entryPruningTailSize;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param entryCapacity Maximum number of entries cached.
     */
    Builder entryCapacity(int entryCapacity);

    /**
     * @return Maximum number of entries cached.
     */
    int entryCapacity();

    /**
     * @param entryPruningTailSize Number of entries to prune at a time.
     */
    Builder entryPruningTailSize(int entryPruningTailSize);

    /**
     * @return Number of entries to prune at a time.
     */
    int entryPruningTailSize();

    MultiThreadedCache build();
  }

  static class BuilderImpl implements Builder {

    protected int entryCapacity;

    private boolean _entryCapacitySet = false;

    protected int entryPruningTailSize;

    private boolean _entryPruningTailSizeSet = false;

    protected BuilderImpl() {}

    protected BuilderImpl(MultiThreadedCache model) {
      this.entryCapacity = model.entryCapacity();
      this._entryCapacitySet = true;
      this.entryPruningTailSize = model.entryPruningTailSize();
      this._entryPruningTailSizeSet = true;
    }

    public Builder entryCapacity(int entryCapacity) {
      this.entryCapacity = entryCapacity;
      this._entryCapacitySet = true;
      return this;
    }

    public int entryCapacity() {
      return this.entryCapacity;
    }

    public Builder entryPruningTailSize(int entryPruningTailSize) {
      this.entryPruningTailSize = entryPruningTailSize;
      this._entryPruningTailSizeSet = true;
      return this;
    }

    public int entryPruningTailSize() {
      return this.entryPruningTailSize;
    }

    public MultiThreadedCache build() {
      if (!this._entryCapacitySet) {
        throw new IllegalArgumentException(
          "Missing value for required field `entryCapacity`"
        );
      }
      if (this._entryCapacitySet && this.entryCapacity() < 1) {
        throw new IllegalArgumentException(
          "`entryCapacity` must be greater than or equal to 1"
        );
      }
      if (this._entryPruningTailSizeSet && this.entryPruningTailSize() < 1) {
        throw new IllegalArgumentException(
          "`entryPruningTailSize` must be greater than or equal to 1"
        );
      }
      return new MultiThreadedCache(this);
    }
  }
}
