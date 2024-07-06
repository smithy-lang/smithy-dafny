// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using $namespace:L;
using $namespace:L.Wrapped;
using TypeConversion = $namespace:L.TypeConversion;
namespace $dafnyNamespace:L.internaldafny.wrapped
{
    public partial class __default 
    {
        public static _IResult<types.I$service:LClient, types._IError> Wrapped$service:L(types._I$serviceConfig:L config) 
        {
            var wrappedConfig = TypeConversion.$configConversionMethod:L(config);
            var impl = new $service:L(wrappedConfig);
            var wrappedClient = new $service:LShim(impl);
            return Result<types.I$service:LClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
