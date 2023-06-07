// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Union;
using Simple.Union.Wrapped;
using TypeConversion = Simple.Union.TypeConversion;
namespace simple.union.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleUnionClient, types._IError> WrappedSimpleUnion(types._ISimpleUnionConfig config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_union__S17_SimpleUnionConfig(config);
            var impl = new SimpleUnion(wrappedConfig);
            var wrappedClient = new SimpleUnionShim(impl);
            return Result<types.ISimpleUnionClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
