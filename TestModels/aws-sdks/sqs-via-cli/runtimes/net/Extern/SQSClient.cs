// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.SQS;
using Wrappers_Compile;
using Amazon.Runtime;
using Com.Amazonaws.Sqs;

// This extern is identified in Dafny code
// that refines the AWS SDK SQS Model
namespace software.amazon.cryptography.services.sqs.internaldafny
{
    public partial class __default
    {

        public static
          _IResult<
            types.ISQSClient,
            types._IError
          >
          SQSClient()
        {
            var client = new AmazonSQSClient();

            return Result<
              types.ISQSClient,
              types._IError
            >
              .create_Success(new SQSShim(client));
        }
    }
}
