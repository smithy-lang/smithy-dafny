// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

using System;
using Dafny.Simple.Extendable.Resources;
using Dafny.Simple.Extendable.Resources.Types;
using Simple.Extendable.Resources;

namespace Simple.Extendable.Resources
{
  public class NativeResource : ExtendableResourceBase
  {
    private readonly IExtendableResource _impl;

    public NativeResource(IExtendableResource nativeImpl)
    {
      this._impl = nativeImpl;
    }

    protected override GetExtendableResourceDataOutput _GetExtendableResourceData(GetExtendableResourceDataInput input)
    {
      return this._impl.GetExtendableResourceData(input);
    }

    protected override GetExtendableResourceErrorsOutput _AlwaysModeledError(GetExtendableResourceErrorsInput input)
    {
      return this._impl.AlwaysModeledError(input);
    }

    protected override GetExtendableResourceErrorsOutput _AlwaysMultipleErrors(GetExtendableResourceErrorsInput input)
    {
      return this._impl.AlwaysMultipleErrors(input);
    }

    protected override GetExtendableResourceErrorsOutput _AlwaysOpaqueError(GetExtendableResourceErrorsInput input)
    {
      if (input.IsSetValue())
      {
        throw new Exception(".NET Hard Coded Exception");
      }

      return this._impl.AlwaysOpaqueError(input);
    }

    public static NativeResource NativeFactory()
    {
      ExtendableResource_Compile.ExtendableResource _nw2 = new ExtendableResource_Compile.ExtendableResource();
      _nw2.__ctor();
      IExtendableResource dafnyResource =
        TypeConversion.FromDafny_N6_simple__N10_extendable__N9_resources__S27_ExtendableResourceReference(_nw2);
      return new NativeResource(dafnyResource);
    }
  }
}


