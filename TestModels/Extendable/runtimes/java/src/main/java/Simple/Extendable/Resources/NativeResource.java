// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package simple.extendable.resources;

import ExtendableResource_Compile.ExtendableResource;
import java.util.Objects;
import simple.extendable.resources.IExtendableResource;
import simple.extendable.resources.ToNative;
import simple.extendable.resources.model.GetExtendableResourceDataInput;
import simple.extendable.resources.model.GetExtendableResourceDataOutput;
import simple.extendable.resources.model.GetExtendableResourceErrorsInput;
import simple.extendable.resources.model.GetExtendableResourceErrorsOutput;

public class NativeResource implements IExtendableResource {

  private final IExtendableResource _impl;

  public NativeResource(final IExtendableResource impl) {
    this._impl = impl;
  }

  @Override
  public GetExtendableResourceDataOutput GetExtendableResourceData(
    GetExtendableResourceDataInput nativeValue
  ) {
    return this._impl.GetExtendableResourceData(nativeValue);
  }

  @Override
  public GetExtendableResourceErrorsOutput AlwaysModeledError(
    GetExtendableResourceErrorsInput nativeValue
  ) {
    return this._impl.AlwaysModeledError(nativeValue);
  }

  @Override
  public GetExtendableResourceErrorsOutput AlwaysMultipleErrors(
    GetExtendableResourceErrorsInput nativeValue
  ) {
    return this._impl.AlwaysMultipleErrors(nativeValue);
  }

  @Override
  public GetExtendableResourceErrorsOutput AlwaysOpaqueError(
    GetExtendableResourceErrorsInput nativeValue
  ) {
    if (Objects.nonNull(nativeValue.value())) {
      throw new RuntimeException("Java Hard Coded Exception");
    }
    return this._impl.AlwaysOpaqueError(nativeValue);
  }

  public static NativeResource NativeFactory() {
    ExtendableResource _nw2 = new ExtendableResource();
    _nw2.__ctor();
    IExtendableResource dafnyResource = ToNative.ExtendableResource(_nw2);
    return new NativeResource(dafnyResource);
  }
}
