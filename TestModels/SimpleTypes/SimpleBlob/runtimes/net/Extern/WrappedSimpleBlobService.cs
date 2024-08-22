// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Types.Blob;
using Simple.Types.Blob.Wrapped;
using TypeConversion = Simple.Types.Blob.TypeConversion;
namespace simple.types.blob.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleTypesBlobClient, types._IError> WrappedSimpleBlob(types._ISimpleBlobConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N5_types__N4_blob__S16_SimpleBlobConfig(config);
            var impl = new SimpleBlob(wrappedConfig);
            var wrappedClient = new SimpleTypesBlobShim(impl);
            return Result<types.ISimpleTypesBlobClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
