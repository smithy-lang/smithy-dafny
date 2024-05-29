// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.LakeFormation;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Lakeformation;

// This extern is identified in Dafny code
// that refines the AWS SDK Model
namespace software.amazon.cryptography.services.lakeformation.internaldafny
{
    public partial class __default
    {
        public static
            _IResult<
                types.ILakeFormationClient,
                types._IError
            >
            LakeFormationClient()
        {
            var client = new AmazonLakeFormationClient();

            return Result<
                    types.ILakeFormationClient,
                    types._IError
                >
                .create_Success(new LakeFormationShim(client));
        }
    }
}
