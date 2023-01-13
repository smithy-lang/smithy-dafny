// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
package example.simpletypes;

import Dafny.Example.Simpletypes.Types.Error;
import Dafny.Example.Simpletypes.Types.Error_Collection;
import Dafny.Example.Simpletypes.Types.Error_Opaque;
import example.simpletypes.model.CollectionOfErrors;
import example.simpletypes.model.EmptyConfig;
import example.simpletypes.model.GetStringInput;
import example.simpletypes.model.GetStringOutput;
import example.simpletypes.model.NativeError;
import example.simpletypes.model.OpaqueError;

public class ToNative {
  public static OpaqueError Error(Error_Opaque dafnyValue) {
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue.dtor_obj());
    return nativeBuilder.build();
  }

  public static CollectionOfErrors Error(Error_Collection dafnyValue) {
    CollectionOfErrors.Builder nativeBuilder = CollectionOfErrors.builder();
    nativeBuilder.list(
        software.amazon.dafny.conversion.ToNative.Aggregate.GenericToList(
        dafnyValue.dtor_list(), 
        ToNative::Error));
    return nativeBuilder.build();
  }

  public static NativeError Error(Error dafnyValue) {
    if (dafnyValue.is_Opaque()) {
      return ToNative.Error((Error_Opaque) dafnyValue);
    }
    if (dafnyValue.is_Collection()) {
      return ToNative.Error((Error_Collection) dafnyValue);
    }
    OpaqueError.Builder nativeBuilder = OpaqueError.builder();
    nativeBuilder.obj(dafnyValue);
    return nativeBuilder.build();
  }

  public static GetStringInput GetStringInput(
      Dafny.Example.Simpletypes.Types.GetStringInput dafnyValue) {
    GetStringInput.Builder nativeBuilder = GetStringInput.builder();
    if (dafnyValue.dtor_stringValue().is_Some()) {
      nativeBuilder.stringValue(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_stringValue().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static GetStringOutput GetStringOutput(
      Dafny.Example.Simpletypes.Types.GetStringOutput dafnyValue) {
    GetStringOutput.Builder nativeBuilder = GetStringOutput.builder();
    if (dafnyValue.dtor_result().is_Some()) {
      nativeBuilder.result(software.amazon.dafny.conversion.ToNative.Simple.String(dafnyValue.dtor_result().dtor_value()));
    }
    return nativeBuilder.build();
  }

  public static EmptyConfig EmptyConfig(Dafny.Example.Simpletypes.Types.EmptyConfig dafnyValue) {
    EmptyConfig.Builder nativeBuilder = EmptyConfig.builder();
    return nativeBuilder.build();
  }
}
