// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.dependencies;

import Dafny.Simple.Dependencies.Types.Error;
import Dafny.Simple.Dependencies.Types.Error_CollectionOfErrors;
import Dafny.Simple.Dependencies.Types.Error_Opaque;
import Dafny.Simple.Dependencies.Types.ISimpleDependenciesClient;
import java.lang.RuntimeException;
import simple.dependencies.model.CollectionOfErrors;
import simple.dependencies.model.OpaqueError;
import simple.dependencies.model.SimpleDependenciesConfig;
import simple.dependencies.model.UseSimpleResourceInput;

public class ToNative {
  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_CollectionOfErrors dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
        software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(), 
        ToNative::Error));
    return nativeBuilder.build();
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_CollectionOfErrors()) {
      return ToNative.Error((Error_CollectionOfErrors) dafnyValue);
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static SimpleDependenciesConfig SimpleDependenciesConfig(
      Dafny.Simple.Dependencies.Types.SimpleDependenciesConfig dafnyValue) {
    SimpleDependenciesConfig.Builder nativeBuilder = SimpleDependenciesConfig.builder();
    if (dafnyValue.dtor_simpleResourcesConfig().is_Some()) {
      nativeBuilder.simpleResourcesConfig(simple.resources.ToNative.SimpleResourcesConfig(dafnyValue.dtor_simpleResourcesConfig().dtor_value()));
    }
    if (dafnyValue.dtor_simpleConstraintsServiceReference().is_Some()) {
      nativeBuilder.simpleConstraintsServiceReference(simple.constraints.ToNative.SimpleConstraints(dafnyValue.dtor_simpleConstraintsServiceReference().dtor_value()));
    }
    if (dafnyValue.dtor_extendableResourceReference().is_Some()) {
      nativeBuilder.extendableResourceReference(simple.extendable.resources.ToNative.ExtendableResource(dafnyValue.dtor_extendableResourceReference().dtor_value()));
    }
    if (dafnyValue.dtor_specialString().is_Some()) {
      nativeBuilder.specialString(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_specialString().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static UseSimpleResourceInput UseSimpleResourceInput(
      Dafny.Simple.Dependencies.Types.UseSimpleResourceInput dafnyValue) {
    UseSimpleResourceInput.Builder nativeBuilder = UseSimpleResourceInput.builder();
    nativeBuilder.value(simple.resources.ToNative.SimpleResource(dafnyValue.dtor_value()));
    nativeBuilder.input(simple.resources.ToNative.GetResourceDataInput(dafnyValue.dtor_input()));
    return nativeBuilder.build();
  }

  public static SimpleDependencies SimpleDependencies(ISimpleDependenciesClient dafnyValue) {
    return new SimpleDependencies(dafnyValue);
  }
}
