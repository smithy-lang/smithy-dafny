// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic; namespace Simple.Resources.Wrapped {
 public class SimpleResourcesShim : Dafny.Simple.Resources.Types.ISimpleResourcesClient {
 public Simple.Resources.SimpleResources _impl;
 public SimpleResourcesShim(Simple.Resources.SimpleResources impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<Dafny.Simple.Resources.Types._IGetResourcesOutput, Dafny.Simple.Resources.Types._IError> GetResources(Dafny.Simple.Resources.Types._IGetResourcesInput request) {
 Simple.Resources.GetResourcesInput unWrappedRequest = TypeConversion.FromDafny_N6_simple__N9_resources__S17_GetResourcesInput(request); try {
 Simple.Resources.GetResourcesOutput wrappedResponse =
 this._impl.GetResources(unWrappedRequest);
 return Wrappers_Compile.Result<Dafny.Simple.Resources.Types._IGetResourcesOutput, Dafny.Simple.Resources.Types._IError>.create_Success(TypeConversion.ToDafny_N6_simple__N9_resources__S18_GetResourcesOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<Dafny.Simple.Resources.Types._IGetResourcesOutput, Dafny.Simple.Resources.Types._IError>.create_Failure(this.ConvertError(ex));
}

}
 private Dafny.Simple.Resources.Types._IError ConvertError(System.Exception error) {
 switch (error) {
 case Simple.Resources.SimpleResourcesException e:
    return TypeConversion.ToDafny_N6_simple__N9_resources__S24_SimpleResourcesException(e);

 default:
    return new Dafny.Simple.Resources.Types.Error_Opaque(error);

}
}
}
}
