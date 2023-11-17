// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviders.model;

import java.util.Objects;

public class CreateCryptographicMaterialsCacheInput {

  /**
   * Which type of local cache to use.
   */
  private final CacheType cache;

  protected CreateCryptographicMaterialsCacheInput(BuilderImpl builder) {
    this.cache = builder.cache();
  }

  /**
   * @return Which type of local cache to use.
   */
  public CacheType cache() {
    return this.cache;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    /**
     * @param cache Which type of local cache to use.
     */
    Builder cache(CacheType cache);

    /**
     * @return Which type of local cache to use.
     */
    CacheType cache();

    CreateCryptographicMaterialsCacheInput build();
  }

  static class BuilderImpl implements Builder {

    protected CacheType cache;

    protected BuilderImpl() {}

    protected BuilderImpl(CreateCryptographicMaterialsCacheInput model) {
      this.cache = model.cache();
    }

    public Builder cache(CacheType cache) {
      this.cache = cache;
      return this;
    }

    public CacheType cache() {
      return this.cache;
    }

    public CreateCryptographicMaterialsCacheInput build() {
      if (Objects.isNull(this.cache())) {
        throw new IllegalArgumentException(
          "Missing value for required field `cache`"
        );
      }
      return new CreateCryptographicMaterialsCacheInput(this);
    }
  }
}
