// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.Glue;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Glue;

// This extern is identified in Dafny code
// that refines the AWS SDK Model
namespace software.amazon.cryptography.services.glue.internaldafny
{
    public partial class __default
    {
        public static
            _IResult<
                types.IGlueClient,
                types._IError
            >
            GlueClient()
        {
            var client = new AmazonGlueClient();

            return Result<
                    types.IGlueClient,
                    types._IError
                >
                .create_Success(new GlueShim(client));
        }
    }
}
