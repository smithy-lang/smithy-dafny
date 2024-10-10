// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.DafnyExtern;
using Simple.DafnyExtern.Wrapped;
using TypeConversion = Simple.DafnyExtern.TypeConversion;
namespace simple.dafnyextern.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleExternClient, types._IError> WrappedSimpleExtern(types._ISimpleExternConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_dafnyExtern__S18_SimpleExternConfig(config);
            var impl = new SimpleExtern(wrappedConfig);
            var wrappedClient = new SimpleExternShim(impl);
            return Result<types.ISimpleExternClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
