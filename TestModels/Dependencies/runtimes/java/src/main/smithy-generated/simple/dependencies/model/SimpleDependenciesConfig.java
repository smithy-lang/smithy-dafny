// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies.model;

import java.util.Objects;
import simple.constraints.SimpleConstraints;
import simple.extendable.resources.ExtendableResource;
import simple.extendable.resources.IExtendableResource;
import simple.resources.model.SimpleResourcesConfig;

public class SimpleDependenciesConfig {
  private final SimpleResourcesConfig simpleResourcesConfig;

  private final SimpleConstraints simpleConstraintsServiceReference;

  private final IExtendableResource extendableResourceReference;

  private final String specialString;

  protected SimpleDependenciesConfig(BuilderImpl builder) {
    this.simpleResourcesConfig = builder.simpleResourcesConfig();
    this.simpleConstraintsServiceReference = builder.simpleConstraintsServiceReference();
    this.extendableResourceReference = builder.extendableResourceReference();
    this.specialString = builder.specialString();
  }

  public SimpleResourcesConfig simpleResourcesConfig() {
    return this.simpleResourcesConfig;
  }

  public SimpleConstraints simpleConstraintsServiceReference() {
    return this.simpleConstraintsServiceReference;
  }

  public IExtendableResource extendableResourceReference() {
    return this.extendableResourceReference;
  }

  public String specialString() {
    return this.specialString;
  }

  public Builder toBuilder() {
    return new BuilderImpl(this);
  }

  public static Builder builder() {
    return new BuilderImpl();
  }

  public interface Builder {
    Builder simpleResourcesConfig(SimpleResourcesConfig simpleResourcesConfig);

    SimpleResourcesConfig simpleResourcesConfig();

    Builder simpleConstraintsServiceReference(SimpleConstraints simpleConstraintsServiceReference);

    SimpleConstraints simpleConstraintsServiceReference();

    Builder extendableResourceReference(IExtendableResource extendableResourceReference);

    IExtendableResource extendableResourceReference();

    Builder specialString(String specialString);

    String specialString();

    SimpleDependenciesConfig build();
  }

  static class BuilderImpl implements Builder {
    protected SimpleResourcesConfig simpleResourcesConfig;

    protected SimpleConstraints simpleConstraintsServiceReference;

    protected IExtendableResource extendableResourceReference;

    protected String specialString;

    protected BuilderImpl() {
    }

    protected BuilderImpl(SimpleDependenciesConfig model) {
      this.simpleResourcesConfig = model.simpleResourcesConfig();
      this.simpleConstraintsServiceReference = model.simpleConstraintsServiceReference();
      this.extendableResourceReference = model.extendableResourceReference();
      this.specialString = model.specialString();
    }

    public Builder simpleResourcesConfig(SimpleResourcesConfig simpleResourcesConfig) {
      this.simpleResourcesConfig = simpleResourcesConfig;
      return this;
    }

    public SimpleResourcesConfig simpleResourcesConfig() {
      return this.simpleResourcesConfig;
    }

    public Builder simpleConstraintsServiceReference(
        SimpleConstraints simpleConstraintsServiceReference) {
      this.simpleConstraintsServiceReference = simpleConstraintsServiceReference;
      return this;
    }

    public SimpleConstraints simpleConstraintsServiceReference() {
      return this.simpleConstraintsServiceReference;
    }

    public Builder extendableResourceReference(IExtendableResource extendableResourceReference) {
      this.extendableResourceReference = ExtendableResource.wrap(extendableResourceReference);
      return this;
    }

    public IExtendableResource extendableResourceReference() {
      return this.extendableResourceReference;
    }

    public Builder specialString(String specialString) {
      this.specialString = specialString;
      return this;
    }

    public String specialString() {
      return this.specialString;
    }

    public SimpleDependenciesConfig build() {
      if (Objects.nonNull(this.specialString()) && this.specialString().length() < 1) {
        throw new IllegalArgumentException("The size of `specialString` must be greater than or equal to 1");
      }
      if (Objects.nonNull(this.specialString()) && this.specialString().length() > 10) {
        throw new IllegalArgumentException("The size of `specialString` must be less than or equal to 10");
      }
      return new SimpleDependenciesConfig(this);
    }
  }
}
