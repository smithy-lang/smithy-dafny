// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class CacheType {
  /**
   * The best choice for most situations. Probably a StormTrackingCache.
   */
  private final DefaultCache defaultCache;

  /**
   * Nothing should ever be cached.
   */
  private final NoCache noCache;

  /**
   * A cache that is NOT safe for use in a multi threaded environment.
   */
  private final SingleThreadedCache singleThreadedCache;

  /**
   * A cache that is safe for use in a multi threaded environment, but no extra functionality.
   */
  private final MultiThreadedCache multiThreadedCache;

  /**
   * A cache that is safe for use in a multi threaded environment,
   * and tries to prevent redundant or overly parallel backend calls.
   */
  private final StormTrackingCache stormTrackingCache;

  protected CacheType(BuilderImpl builder) {
    this.defaultCache = builder.defaultCache();
    this.noCache = builder.noCache();
    this.singleThreadedCache = builder.singleThreadedCache();
    this.multiThreadedCache = builder.multiThreadedCache();
    this.stormTrackingCache = builder.stormTrackingCache();
  }

  /**
   * @return The best choice for most situations. Probably a StormTrackingCache.
   */
  public DefaultCache defaultCache() {
    return this.defaultCache;
  }

  /**
   * @return Nothing should ever be cached.
   */
  public NoCache noCache() {
    return this.noCache;
  }

  /**
   * @return A cache that is NOT safe for use in a multi threaded environment.
   */
  public SingleThreadedCache singleThreadedCache() {
    return this.singleThreadedCache;
  }

  /**
   * @return A cache that is safe for use in a multi threaded environment, but no extra functionality.
   */
  public MultiThreadedCache multiThreadedCache() {
    return this.multiThreadedCache;
  }

  /**
   * @return A cache that is safe for use in a multi threaded environment,
   * and tries to prevent redundant or overly parallel backend calls.
   */
  public StormTrackingCache stormTrackingCache() {
    return this.stormTrackingCache;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param defaultCache The best choice for most situations. Probably a StormTrackingCache.
     */
    Builder defaultCache(DefaultCache defaultCache);

    /**
     * @return The best choice for most situations. Probably a StormTrackingCache.
     */
    DefaultCache defaultCache();

    /**
     * @param noCache Nothing should ever be cached.
     */
    Builder noCache(NoCache noCache);

    /**
     * @return Nothing should ever be cached.
     */
    NoCache noCache();

    /**
     * @param singleThreadedCache A cache that is NOT safe for use in a multi threaded environment.
     */
    Builder singleThreadedCache(SingleThreadedCache singleThreadedCache);

    /**
     * @return A cache that is NOT safe for use in a multi threaded environment.
     */
    SingleThreadedCache singleThreadedCache();

    /**
     * @param multiThreadedCache A cache that is safe for use in a multi threaded environment, but no extra functionality.
     */
    Builder multiThreadedCache(MultiThreadedCache multiThreadedCache);

    /**
     * @return A cache that is safe for use in a multi threaded environment, but no extra functionality.
     */
    MultiThreadedCache multiThreadedCache();

    /**
     * @param stormTrackingCache A cache that is safe for use in a multi threaded environment,
     * and tries to prevent redundant or overly parallel backend calls.
     */
    Builder stormTrackingCache(StormTrackingCache stormTrackingCache);

    /**
     * @return A cache that is safe for use in a multi threaded environment,
     * and tries to prevent redundant or overly parallel backend calls.
     */
    StormTrackingCache stormTrackingCache();

    CacheType build();
  }

  static class BuilderImpl implements Builder {
    protected DefaultCache defaultCache;

    protected NoCache noCache;

    protected SingleThreadedCache singleThreadedCache;

    protected MultiThreadedCache multiThreadedCache;

    protected StormTrackingCache stormTrackingCache;

    protected BuilderImpl() {
    }

    protected BuilderImpl(CacheType model) {
      this.defaultCache = model.defaultCache();
      this.noCache = model.noCache();
      this.singleThreadedCache = model.singleThreadedCache();
      this.multiThreadedCache = model.multiThreadedCache();
      this.stormTrackingCache = model.stormTrackingCache();
    }

    public Builder defaultCache(DefaultCache defaultCache) {
      this.defaultCache = defaultCache;
      return this;
    }

    public DefaultCache defaultCache() {
      return this.defaultCache;
    }

    public Builder noCache(NoCache noCache) {
      this.noCache = noCache;
      return this;
    }

    public NoCache noCache() {
      return this.noCache;
    }

    public Builder singleThreadedCache(SingleThreadedCache singleThreadedCache) {
      this.singleThreadedCache = singleThreadedCache;
      return this;
    }

    public SingleThreadedCache singleThreadedCache() {
      return this.singleThreadedCache;
    }

    public Builder multiThreadedCache(MultiThreadedCache multiThreadedCache) {
      this.multiThreadedCache = multiThreadedCache;
      return this;
    }

    public MultiThreadedCache multiThreadedCache() {
      return this.multiThreadedCache;
    }

    public Builder stormTrackingCache(StormTrackingCache stormTrackingCache) {
      this.stormTrackingCache = stormTrackingCache;
      return this;
    }

    public StormTrackingCache stormTrackingCache() {
      return this.stormTrackingCache;
    }

    public CacheType build() {
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException("`CacheType` is a Union. A Union MUST have one and only one value set.");
      }
      return new CacheType(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = {this.defaultCache, this.noCache, this.singleThreadedCache, this.multiThreadedCache, this.stormTrackingCache};
      boolean haveOneNonNull = false;
      for (Object o : allValues) {
        if (Objects.nonNull(o)) {
          if (haveOneNonNull) {
            return false;
          }
          haveOneNonNull = true;
        }
      }
      return haveOneNonNull;
    }
  }
}
