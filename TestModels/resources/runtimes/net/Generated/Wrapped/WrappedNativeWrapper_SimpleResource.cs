// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// ReSharper disable RedundantUsingDirective
// ReSharper disable RedundantNameQualifier
// ReSharper disable SuggestVarOrType_SimpleTypes
 using System;
 using _System;
 using Wrappers_Compile;

 namespace Simple.Resources.Wrapped {
 internal class WrappedNativeWrapper_SimpleResource : Dafny.Simple.Resources.Types.ISimpleResource 
 {
 internal readonly SimpleResourceBase _impl;
 public WrappedNativeWrapper_SimpleResource(SimpleResourceBase nativeImpl)
 {
 _impl = nativeImpl;
}
 public Wrappers_Compile._IResult<Dafny.Simple.Resources.Types._IGetResourceDataOutput, Dafny.Simple.Resources.Types._IError> GetResourceData(Dafny.Simple.Resources.Types._IGetResourceDataInput input)
 {
 void validateOutput(Simple.Resources.GetResourceDataOutput nativeOutput) {
 try { nativeOutput.Validate(); } catch (ArgumentException e)
 {
 var message = $"Output of {_impl}._GetResourceData is invalid. {e.Message}";
 throw new SimpleResourcesException(message);
}
}
 Simple.Resources.GetResourceDataInput nativeInput = TypeConversion.FromDafny_N6_simple__N9_resources__S20_GetResourceDataInput(input);
 try {
 Simple.Resources.GetResourceDataOutput nativeOutput = _impl.GetResourceData(nativeInput);
 _ = nativeOutput ?? throw new SimpleResourcesException($"{_impl}._GetResourceData returned null, should be {typeof(Simple.Resources.GetResourceDataOutput)}");
 validateOutput(nativeOutput);
 return Wrappers_Compile.Result<Dafny.Simple.Resources.Types._IGetResourceDataOutput, Dafny.Simple.Resources.Types._IError>.create_Success(TypeConversion.ToDafny_N6_simple__N9_resources__S21_GetResourceDataOutput(nativeOutput));
}
 catch(Exception e)
 {
 return Wrappers_Compile.Result<Dafny.Simple.Resources.Types._IGetResourceDataOutput, Dafny.Simple.Resources.Types._IError>.create_Failure(TypeConversion.ToDafny_CommonError(e));
}
}
 public Wrappers_Compile._IResult<Dafny.Simple.Resources.Types._IGetResourceDataOutput, Dafny.Simple.Resources.Types._IError> GetResourceData_k(Dafny.Simple.Resources.Types._IGetResourceDataInput input)
 {
 throw new SimpleResourcesException("Not supported at this time.");
}
}
}
