// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Aggregate;
using Simple.Aggregate.Wrapped;
using TypeConversion = Simple.Aggregate.TypeConversion;
namespace simple.aggregate.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleAggregateClient, types._IError> WrappedSimpleAggregate(types._ISimpleAggregateConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N9_aggregate__S21_SimpleAggregateConfig(config);
            var impl = new SimpleAggregate(wrappedConfig);
            var wrappedClient = new SimpleAggregateShim(impl);
            return Result<types.ISimpleAggregateClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
