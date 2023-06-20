// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.SmithyLong;
using Simple.Types.SmithyLong.Wrapped;
using TypeConversion = Simple.Types.SmithyLong.TypeConversion ;
namespace simple.types.smithylong.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleTypesLongClient, types._IError> WrappedSimpleLong(types._ISimpleLongConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N10_smithyLong__S16_SimpleLongConfig(config);
            var impl = new SimpleLong(wrappedConfig);
            var wrappedClient = new SimpleTypesLongShim(impl);
            return Result<types.ISimpleTypesLongClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
