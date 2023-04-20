// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies;

import Dafny.Simple.Constraints.Types.ISimpleConstraintsClient;
import Dafny.Simple.Dependencies.Types.Error;
import Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient;
import Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig;
import Dafny.Simple.Dependencies.Types.UseSimpleResourceInput;
import Dafny.Simple.Extendable.Resources.Types.IExtendableResource;
import Dafny.Simple.Resources.Types.GetResourceDataInput;
import Dafny.Simple.Resources.Types.ISimpleResource;
import Dafny.Simple.Resources.Types.SimpleResourcesConfig;
import Wrappers_Compile.Option;
import dafny.DafnySequence;
import java.lang.Character;
import java.lang.RuntimeException;
import java.util.Objects;
import simple.dependencies.model.CollectionOfErrors;
import simple.dependencies.model.OpaqueError;

public class ToDafny {
  public static Error Error(RuntimeException nativeValue) {
    if (nativeValue instanceof OpaqueError) {
      return ToDafny.Error((OpaqueError) nativeValue);
    }
    if (nativeValue instanceof CollectionOfErrors) {
      return ToDafny.Error((CollectionOfErrors) nativeValue);
    }
    return Error.create_Opaque(nativeValue);
  }

  public static Error Error(OpaqueError nativeValue) {
    return Error.create_Opaque(nativeValue.obj());
  }

  public static Error Error(CollectionOfErrors nativeValue) {
    DafnySequence<? extends Error> list = software.amazon.dafny.conversion.ToDafny.Aggregate.GenericToSequence(
        nativeValue.list(), 
        ToDafny::Error, 
        Error._typeDescriptor());
    return Error.create_CollectionOfErrors(list);
  }

  public static SimpleDependenciesConfig SimpleDependenciesConfig(
      simple.dependencies.model.SimpleDependenciesConfig nativeValue) {
    Option<SimpleResourcesConfig> simpleResourcesConfig;
    simpleResourcesConfig = Objects.nonNull(nativeValue.simpleResourcesConfig()) ?
        Option.create_Some(simple.resources.ToDafny.SimpleResourcesConfig(nativeValue.simpleResourcesConfig()))
        : Option.create_None();
    Option<ISimpleConstraintsClient> simpleConstraintsServiceReference;
    simpleConstraintsServiceReference = Objects.nonNull(nativeValue.simpleConstraintsServiceReference()) ?
        Option.create_Some(simple.constraints.ToDafny.SimpleConstraints(nativeValue.simpleConstraintsServiceReference()))
        : Option.create_None();
    Option<IExtendableResource> extendableResourceReference;
    extendableResourceReference = Objects.nonNull(nativeValue.extendableResourceReference()) ?
        Option.create_Some(simple.extendable.resources.ToDafny.ExtendableResource(nativeValue.extendableResourceReference()))
        : Option.create_None();
    Option<DafnySequence<? extends Character>> specialString;
    specialString = Objects.nonNull(nativeValue.specialString()) ?
        Option.create_Some(software.amazon.dafny.conversion.ToDafny.Simple.CharacterSequence(nativeValue.specialString()))
        : Option.create_None();
    return new SimpleDependenciesConfig(simpleResourcesConfig, simpleConstraintsServiceReference, extendableResourceReference, specialString);
  }

  public static UseSimpleResourceInput UseSimpleResourceInput(
      simple.dependencies.model.UseSimpleResourceInput nativeValue) {
    ISimpleResource value;
    value = simple.resources.ToDafny.SimpleResource(nativeValue.value());
    GetResourceDataInput input;
    input = simple.resources.ToDafny.GetResourceDataInput(nativeValue.input());
    return new UseSimpleResourceInput(value, input);
  }

  public static ISimpleDependenciesClient SimpleDependencies(SimpleDependencies nativeValue) {
    return nativeValue.impl();
  }
}
