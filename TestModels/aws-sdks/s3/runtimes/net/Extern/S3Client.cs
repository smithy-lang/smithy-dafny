// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.S3;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.S3;

namespace software.amazon.cryptography.services.s3.internaldafny
{
    public partial class __default
    {

        public static
          _IResult<
            types.IS3Client,
            types._IError
          >
          S3Client()
        {
            var client = new AmazonS3Client();

            return Result<
              types.IS3Client,
              types._IError
            >
              .create_Success(new S3Shim(client));
        }

        public static _IOption<bool> RegionMatch(
            software.amazon.cryptography.services.s3.internaldafny.types.IS3Client client,
            Dafny.ISequence<char> region)
        {
            string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
            // We should never be passing anything other than S3Shim as the 'client'.
            // If this cast fails, that indicates that there is something wrong with
            // our code generation.
            IAmazonS3 nativeClient = ((S3Shim)client)._impl;
            return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
        }
    }
}
