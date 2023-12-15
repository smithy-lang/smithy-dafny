// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.DafnyExternV2;
using Simple.DafnyExternV2.Wrapped;
using TypeConversion = Simple.DafnyExternV2.TypeConversion ;
namespace simple.dafnyexternv2.internaldafny.wrapped
{
    public partial class __default {
        public static _IResult<types.ISimpleExternV2Client, types._IError> WrappedSimpleExternV2(types._ISimpleExternV2Config config) {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N13_dafnyExternV2__S20_SimpleExternV2Config(config);
            var impl = new SimpleExternV2(wrappedConfig);
            var wrappedClient = new SimpleExternV2Shim(impl);
            return Result<types.ISimpleExternV2Client, types._IError>.create_Success(wrappedClient);
        }
    }
}
