// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public class CreateCryptographicMaterialsCacheInput {
  private final int entryCapacity;

  private final int entryPruningTailSize;

  private final int gracePeriod;

  private final int graceInterval;

  private final int fanOut;

  protected CreateCryptographicMaterialsCacheInput(BuilderImpl builder) {
    this.entryCapacity = builder.entryCapacity();
    this.entryPruningTailSize = builder.entryPruningTailSize();
    this.gracePeriod = builder.gracePeriod();
    this.graceInterval = builder.graceInterval();
    this.fanOut = builder.fanOut();
  }

  public int entryCapacity() {
    return this.entryCapacity;
  }

  public int entryPruningTailSize() {
    return this.entryPruningTailSize;
  }

  public int gracePeriod() {
    return this.gracePeriod;
  }

  public int graceInterval() {
    return this.graceInterval;
  }

  public int fanOut() {
    return this.fanOut;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder entryCapacity(int entryCapacity);

    int entryCapacity();

    Builder entryPruningTailSize(int entryPruningTailSize);

    int entryPruningTailSize();

    Builder gracePeriod(int gracePeriod);

    int gracePeriod();

    Builder graceInterval(int graceInterval);

    int graceInterval();

    Builder fanOut(int fanOut);

    int fanOut();

    CreateCryptographicMaterialsCacheInput build();
  }

  static class BuilderImpl implements Builder {
    protected int entryCapacity;

    private boolean _entryCapacitySet = false;

    protected int entryPruningTailSize;

    private boolean _entryPruningTailSizeSet = false;

    protected int gracePeriod;

    private boolean _gracePeriodSet = false;

    protected int graceInterval;

    private boolean _graceIntervalSet = false;

    protected int fanOut;

    private boolean _fanOutSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CreateCryptographicMaterialsCacheInput model) {
      this.entryCapacity = model.entryCapacity();
      this._entryCapacitySet = true;
      this.entryPruningTailSize = model.entryPruningTailSize();
      this._entryPruningTailSizeSet = true;
      this.gracePeriod = model.gracePeriod();
      this._gracePeriodSet = true;
      this.graceInterval = model.graceInterval();
      this._graceIntervalSet = true;
      this.fanOut = model.fanOut();
      this._fanOutSet = true;
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

    public CreateCryptographicMaterialsCacheInput build() {
      if (!this._entryCapacitySet) {
        throw new IllegalArgumentException("Missing value for required field `entryCapacity`");
      }
      if (this._entryCapacitySet && this.entryCapacity() < 0) {
        throw new IllegalArgumentException("`entryCapacity` must be greater than or equal to 0");
      }
      if (this._entryPruningTailSizeSet && this.entryPruningTailSize() < 0) {
        throw new IllegalArgumentException("`entryPruningTailSize` must be greater than or equal to 0");
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
      return new CreateCryptographicMaterialsCacheInput(this);
    }
  }
}
