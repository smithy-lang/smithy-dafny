// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.$service:L;
using Wrappers_Compile;
using Amazon.Runtime;
using $namespace:L;

// This extern is identified in Dafny code
// that refines the AWS SDK Model
namespace $dafnyNamespace:L
{
  public partial class __default
  {
    public static
        _IResult<
            types.I$service:LClient,
            types._IError
        >
        $sdkID:LClient()
    {
      var client = new Amazon$sdkID:LClient();

      return Result<
              types.I$sdkID:LClient,
              types._IError
          >
          .create_Success(new $sdkID:LShim(client));
    }
  }
}