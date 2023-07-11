// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

public class StormTrackerSettings {
  /**
   * How many seconds before expiration should an attempt be made to refresh the materials.
   *   If zero, use a simple cache with no storm tracking.
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

  /**
   * How many milliseconds should a thread sleep if fanOut is exceeded
   */
  private final int sleepMilli;

  protected StormTrackerSettings(BuilderImpl builder) {
    this.gracePeriod = builder.gracePeriod();
    this.graceInterval = builder.graceInterval();
    this.fanOut = builder.fanOut();
    this.inFlightTTL = builder.inFlightTTL();
    this.sleepMilli = builder.sleepMilli();
  }

  /**
   * @return How many seconds before expiration should an attempt be made to refresh the materials.
   *   If zero, use a simple cache with no storm tracking.
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

  /**
   * @return How many milliseconds should a thread sleep if fanOut is exceeded
   */
  public int sleepMilli() {
    return this.sleepMilli;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param gracePeriod How many seconds before expiration should an attempt be made to refresh the materials.
     *   If zero, use a simple cache with no storm tracking.
     */
    Builder gracePeriod(int gracePeriod);

    /**
     * @return How many seconds before expiration should an attempt be made to refresh the materials.
     *   If zero, use a simple cache with no storm tracking.
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

    /**
     * @param sleepMilli How many milliseconds should a thread sleep if fanOut is exceeded
     */
    Builder sleepMilli(int sleepMilli);

    /**
     * @return How many milliseconds should a thread sleep if fanOut is exceeded
     */
    int sleepMilli();

    StormTrackerSettings build();
  }

  static class BuilderImpl implements Builder {
    protected int gracePeriod;

    private boolean _gracePeriodSet = false;

    protected int graceInterval;

    private boolean _graceIntervalSet = false;

    protected int fanOut;

    private boolean _fanOutSet = false;

    protected int inFlightTTL;

    private boolean _inFlightTTLSet = false;

    protected int sleepMilli;

    private boolean _sleepMilliSet = false;

    protected BuilderImpl() {
    }

    protected BuilderImpl(StormTrackerSettings model) {
      this.gracePeriod = model.gracePeriod();
      this._gracePeriodSet = true;
      this.graceInterval = model.graceInterval();
      this._graceIntervalSet = true;
      this.fanOut = model.fanOut();
      this._fanOutSet = true;
      this.inFlightTTL = model.inFlightTTL();
      this._inFlightTTLSet = true;
      this.sleepMilli = model.sleepMilli();
      this._sleepMilliSet = true;
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

    public Builder sleepMilli(int sleepMilli) {
      this.sleepMilli = sleepMilli;
      this._sleepMilliSet = true;
      return this;
    }

    public int sleepMilli() {
      return this.sleepMilli;
    }

    public StormTrackerSettings build() {
      if (!this._gracePeriodSet) {
        throw new IllegalArgumentException("Missing value for required field `gracePeriod`");
      }
      if (this._gracePeriodSet && this.gracePeriod() < 0) {
        throw new IllegalArgumentException("`gracePeriod` must be greater than or equal to 0");
      }
      if (!this._graceIntervalSet) {
        throw new IllegalArgumentException("Missing value for required field `graceInterval`");
      }
      if (this._graceIntervalSet && this.graceInterval() < 1) {
        throw new IllegalArgumentException("`graceInterval` must be greater than or equal to 1");
      }
      if (!this._fanOutSet) {
        throw new IllegalArgumentException("Missing value for required field `fanOut`");
      }
      if (this._fanOutSet && this.fanOut() < 1) {
        throw new IllegalArgumentException("`fanOut` must be greater than or equal to 1");
      }
      if (!this._inFlightTTLSet) {
        throw new IllegalArgumentException("Missing value for required field `inFlightTTL`");
      }
      if (this._inFlightTTLSet && this.inFlightTTL() < 1) {
        throw new IllegalArgumentException("`inFlightTTL` must be greater than or equal to 1");
      }
      if (!this._sleepMilliSet) {
        throw new IllegalArgumentException("Missing value for required field `sleepMilli`");
      }
      if (this._sleepMilliSet && this.sleepMilli() < 1) {
        throw new IllegalArgumentException("`sleepMilli` must be greater than or equal to 1");
      }
      return new StormTrackerSettings(this);
    }
  }
}
