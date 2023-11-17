// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.keystore.model;

import java.util.Objects;

public class KMSConfiguration {

  private final String kmsKeyArn;

  protected KMSConfiguration(BuilderImpl builder) {
    this.kmsKeyArn = builder.kmsKeyArn();
  }

  public String kmsKeyArn() {
    return this.kmsKeyArn;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder kmsKeyArn(String kmsKeyArn);

    String kmsKeyArn();

    KMSConfiguration build();
  }

  static class BuilderImpl implements Builder {

    protected String kmsKeyArn;

    protected BuilderImpl() {}

    protected BuilderImpl(KMSConfiguration model) {
      this.kmsKeyArn = model.kmsKeyArn();
    }

    public Builder kmsKeyArn(String kmsKeyArn) {
      this.kmsKeyArn = kmsKeyArn;
      return this;
    }

    public String kmsKeyArn() {
      return this.kmsKeyArn;
    }

    public KMSConfiguration build() {
      if (Objects.nonNull(this.kmsKeyArn()) && this.kmsKeyArn().length() < 1) {
        throw new IllegalArgumentException(
          "The size of `kmsKeyArn` must be greater than or equal to 1"
        );
      }
      if (
        Objects.nonNull(this.kmsKeyArn()) && this.kmsKeyArn().length() > 2048
      ) {
        throw new IllegalArgumentException(
          "The size of `kmsKeyArn` must be less than or equal to 2048"
        );
      }
      if (!onlyOneNonNull()) {
        throw new IllegalArgumentException(
          "`KMSConfiguration` is a Union. A Union MUST have one and only one value set."
        );
      }
      return new KMSConfiguration(this);
    }

    private boolean onlyOneNonNull() {
      Object[] allValues = { this.kmsKeyArn };
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
