// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package software.amazon.cryptography.materialproviderstestvectorkeys.model;

import java.util.Objects;

public class TestVectorCmmInput {

  private final KeyDescription keyDescription;

  private final CmmOperation forOperation;

  protected TestVectorCmmInput(BuilderImpl builder) {
    this.keyDescription = builder.keyDescription();
    this.forOperation = builder.forOperation();
  }

  public KeyDescription keyDescription() {
    return this.keyDescription;
  }

  public CmmOperation forOperation() {
    return this.forOperation;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder keyDescription(KeyDescription keyDescription);

    KeyDescription keyDescription();

    Builder forOperation(CmmOperation forOperation);

    CmmOperation forOperation();

    TestVectorCmmInput build();
  }

  static class BuilderImpl implements Builder {

    protected KeyDescription keyDescription;

    protected CmmOperation forOperation;

    protected BuilderImpl() {}

    protected BuilderImpl(TestVectorCmmInput model) {
      this.keyDescription = model.keyDescription();
      this.forOperation = model.forOperation();
    }

    public Builder keyDescription(KeyDescription keyDescription) {
      this.keyDescription = keyDescription;
      return this;
    }

    public KeyDescription keyDescription() {
      return this.keyDescription;
    }

    public Builder forOperation(CmmOperation forOperation) {
      this.forOperation = forOperation;
      return this;
    }

    public CmmOperation forOperation() {
      return this.forOperation;
    }

    public TestVectorCmmInput build() {
      if (Objects.isNull(this.keyDescription())) {
        throw new IllegalArgumentException(
          "Missing value for required field `keyDescription`"
        );
      }
      if (Objects.isNull(this.forOperation())) {
        throw new IllegalArgumentException(
          "Missing value for required field `forOperation`"
        );
      }
      return new TestVectorCmmInput(this);
    }
  }
}
