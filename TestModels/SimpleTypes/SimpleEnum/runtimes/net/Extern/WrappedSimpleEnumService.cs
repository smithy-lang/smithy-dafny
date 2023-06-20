// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.SmithyEnum;
using Simple.Types.SmithyEnum.Wrapped;
using TypeConversion = Simple.Types.SmithyEnum.TypeConversion ;
namespace simple.types.smithyenum.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleTypesEnumClient, types._IError> WrappedSimpleEnum(types._ISimpleEnumConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N10_smithyEnum__S16_SimpleEnumConfig(config);
            var impl = new SimpleEnum(wrappedConfig);
            var wrappedClient = new SimpleTypesEnumShim(impl);
            return Result<types.ISimpleTypesEnumClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
