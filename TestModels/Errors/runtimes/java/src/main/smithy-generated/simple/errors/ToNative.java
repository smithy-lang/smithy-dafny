// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package simple.errors;

import Dafny.Simple.Errors.Types.Error;
import Dafny.Simple.Errors.Types.Error_CollectionOfErrors;
import Dafny.Simple.Errors.Types.Error_Opaque;
import Dafny.Simple.Errors.Types.Error_SimpleErrorsException;
import simple.errors.model.CollectionOfErrors;
import simple.errors.model.GetErrorsInput;
import simple.errors.model.GetErrorsOutput;
import simple.errors.model.OpaqueError;
import simple.errors.model.SimpleErrorsConfig;
import simple.errors.model.SimpleErrorsException;

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

  public static SimpleErrorsException Error(Error_SimpleErrorsException dafnyValue) {
    SimpleErrorsException.Builder nativeBuilder = SimpleErrorsException.builder();
    nativeBuilder.message(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_message()));
    return nativeBuilder.build();
  }

  public static RuntimeException Error(Error dafnyValue) {
    if (dafnyValue.is_SimpleErrorsException()) {
      return ToNative.Error((Error_SimpleErrorsException) dafnyValue);
    }
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

  public static GetErrorsInput GetErrorsInput(Dafny.Simple.Errors.Types.GetErrorsInput dafnyValue) {
    GetErrorsInput.Builder nativeBuilder = GetErrorsInput.builder();
    if (dafnyValue.dtor_value().is_Some()) {
      nativeBuilder.value(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_value().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static SimpleErrorsConfig SimpleErrorsConfig(
      Dafny.Simple.Errors.Types.SimpleErrorsConfig dafnyValue) {
    SimpleErrorsConfig.Builder nativeBuilder = SimpleErrorsConfig.builder();
    return nativeBuilder.build();
  }

  public static GetErrorsOutput GetErrorsOutput(
      Dafny.Simple.Errors.Types.GetErrorsOutput dafnyValue) {
    GetErrorsOutput.Builder nativeBuilder = GetErrorsOutput.builder();
    if (dafnyValue.dtor_value().is_Some()) {
      nativeBuilder.value(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_value().dtor_value()));
    }
    return nativeBuilder.build();
  }
}
