// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
using System;
 using System.IO;
 using System.Collections.Generic;
 using Simple.Aggregate;
 using Dafny.Simple.Aggregate.Types; namespace Simple.Aggregate {
 public class SimpleAggregate {
 private readonly ISimpleAggregateClient _impl;
 public SimpleAggregate(Simple.Aggregate.SimpleAggregateConfig input)
 {
 Dafny.Simple.Aggregate.Types._ISimpleAggregateConfig internalInput = TypeConversion.ToDafny_N6_simple__N9_aggregate__S21_SimpleAggregateConfig(input);
 var result = Dafny.Simple.Aggregate.__default.SimpleAggregate(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 this._impl = result.dtor_value;
}
 public Simple.Aggregate.GetAggregateOutput GetAggregate(Simple.Aggregate.GetAggregateInput input) {
 Dafny.Simple.Aggregate.Types._IGetAggregateInput internalInput = TypeConversion.ToDafny_N6_simple__N9_aggregate__S17_GetAggregateInput(input);
 Wrappers_Compile._IResult<Dafny.Simple.Aggregate.Types._IGetAggregateOutput, Dafny.Simple.Aggregate.Types._IError> result = _impl.GetAggregate(internalInput);
 if (result.is_Failure) throw TypeConversion.FromDafny_CommonError(result.dtor_error);
 return TypeConversion.FromDafny_N6_simple__N9_aggregate__S18_GetAggregateOutput(result.dtor_value);
}
}
}
