// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.KeyManagementService;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Kms;

// This extern is identified in Dafny code
// that refines the AWS SDK KMS Model
namespace software.amazon.cryptography.services.kms.internaldafny
{
    public partial class __default
    {

        public static
          _IResult<
            types.IKMSClient,
            types._IError
          >
          KMSClient()
        {
            // var region = RegionEndpoint.GetBySystemName("us-west-2");
            // TODO add user agent, endpoint, and region
            var client = new AmazonKeyManagementServiceClient();

            return Result<
              types.IKMSClient,
              types._IError
            >
              .create_Success(new KeyManagementServiceShim(client));
        }

        public static _IOption<bool> RegionMatch(
            software.amazon.cryptography.services.kms.internaldafny.types.IKMSClient client,
            Dafny.ISequence<char> region)
        {
            string regionStr = TypeConversion.FromDafny_N6_smithy__N3_api__S6_String(region);
            // We should never be passing anything other than KeyManagementServiceShim as the 'client'.
            // If this cast fails, that indicates that there is something wrong with
            // our code generation.
            IAmazonKeyManagementService nativeClient = ((KeyManagementServiceShim)client)._impl;
            return new Option_Some<bool>(nativeClient.Config.RegionEndpoint.SystemName.Equals(regionStr));
        }
    }
}
