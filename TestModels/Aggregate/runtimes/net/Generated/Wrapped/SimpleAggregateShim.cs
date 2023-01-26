// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic; namespace Simple.Aggregate.Wrapped {
 public class SimpleAggregateShim : Dafny.Simple.Aggregate.Types.ISimpleAggregateClient {
 public Simple.Aggregate.SimpleAggregate _impl;
 public SimpleAggregateShim(Simple.Aggregate.SimpleAggregate impl) {
    this._impl = impl;
}
 public Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> GetAggregate(Dafny.Simple.Aggregate.Types._IGetAggregateInput request) {
 Simple.Aggregate.GetAggregateInput unWrappedRequest = TypeConversion.FromDafny_N6_simple__N9_aggregate__S17_GetAggregateInput(request); try {
 Simple.Aggregate.GetAggregateOutput wrappedResponse =
 this._impl.GetAggregate(unWrappedRequest);
 return Wrappers_Compile.Result<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError>.create_Success(TypeConversion.ToDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput(wrappedResponse));
} catch (System.Exception ex) {
    return Wrappers_Compile.Result<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError>.create_Failure(this.ConvertError(ex));
}

}
 private Dafny.Simple.Aggregate.Types._IError ConvertError(System.Exception error) {
 switch (error) {

 default:
    return new Dafny.Simple.Aggregate.Types.Error_Opaque(error);

}
}
}
}
