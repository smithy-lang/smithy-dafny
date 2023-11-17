// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

/**
 * The best choice for most situations. Probably a StormTrackingCache.
 */
public class DefaultCache {

  /**
   * Maximum number of entries cached.
   */
  private final int entryCapacity;

  protected DefaultCache(BuilderImpl builder) {
    this.entryCapacity = builder.entryCapacity();
  }

  /**
   * @return Maximum number of entries cached.
   */
  public int entryCapacity() {
    return this.entryCapacity;
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

    DefaultCache build();
  }

  static class BuilderImpl implements Builder {

    protected int entryCapacity;

    private boolean _entryCapacitySet = false;

    protected BuilderImpl() {}

    protected BuilderImpl(DefaultCache model) {
      this.entryCapacity = model.entryCapacity();
      this._entryCapacitySet = true;
    }

    public Builder entryCapacity(int entryCapacity) {
      this.entryCapacity = entryCapacity;
      this._entryCapacitySet = true;
      return this;
    }

    public int entryCapacity() {
      return this.entryCapacity;
    }

    public DefaultCache build() {
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
      return new DefaultCache(this);
    }
  }
}
