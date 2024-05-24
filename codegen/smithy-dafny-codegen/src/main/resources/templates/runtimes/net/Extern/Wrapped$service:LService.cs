// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using %NAMESPACE%;
using %NAMESPACE%.Wrapped;
using TypeConversion = %NAMESPACE%.TypeConversion;
namespace %DAFNY_NAMESPACE%.internaldafny.wrapped
{
    public partial class __default 
    {
        public static _IResult<types.I%SERVICE%Client, types._IError> Wrapped%SERVICE%(types._I%SERVICE_CONFIG% config) 
        {
            var wrappedConfig = TypeConversion.%CONFIG_CONVERSION_METHOD%(config);
            var impl = new %SERVICE%(wrappedConfig);
            var wrappedClient = new %SERVICE%Shim(impl);
            return Result<types.I%SERVICE%Client, types._IError>.create_Success(wrappedClient);
        }
    }
}
