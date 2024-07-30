// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Amazon;
using Amazon.$serviceName:L;
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
            types.I$sdkID:LClient,
            types._IError
        >
        $sdkID:LClient()
    {
      var client = new $sdkClientName:L();

      return Result<
              types.I$sdkID:LClient,
              types._IError
          >
          .create_Success(new $serviceName:LShim(client));
    }
  }
}
