// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.List;
import java.util.Objects;

public class MultiKeyring {

  private final KeyDescription generator;

  private final List<KeyDescription> childKeyrings;

  protected MultiKeyring(BuilderImpl builder) {
    this.generator = builder.generator();
    this.childKeyrings = builder.childKeyrings();
  }

  public KeyDescription generator() {
    return this.generator;
  }

  public List<KeyDescription> childKeyrings() {
    return this.childKeyrings;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder generator(KeyDescription generator);

    KeyDescription generator();

    Builder childKeyrings(List<KeyDescription> childKeyrings);

    List<KeyDescription> childKeyrings();

    MultiKeyring build();
  }

  static class BuilderImpl implements Builder {

    protected KeyDescription generator;

    protected List<KeyDescription> childKeyrings;

    protected BuilderImpl() {}

    protected BuilderImpl(MultiKeyring model) {
      this.generator = model.generator();
      this.childKeyrings = model.childKeyrings();
    }

    public Builder generator(KeyDescription generator) {
      this.generator = generator;
      return this;
    }

    public KeyDescription generator() {
      return this.generator;
    }

    public Builder childKeyrings(List<KeyDescription> childKeyrings) {
      this.childKeyrings = childKeyrings;
      return this;
    }

    public List<KeyDescription> childKeyrings() {
      return this.childKeyrings;
    }

    public MultiKeyring build() {
      if (Objects.isNull(this.childKeyrings())) {
        throw new IllegalArgumentException(
          "Missing value for required field `childKeyrings`"
        );
      }
      return new MultiKeyring(this);
    }
  }
}
