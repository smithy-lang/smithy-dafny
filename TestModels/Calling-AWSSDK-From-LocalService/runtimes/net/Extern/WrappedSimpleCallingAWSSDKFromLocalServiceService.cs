// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.CallingAWSSDKFromLocalService;
using Simple.CallingAWSSDKFromLocalService.Wrapped;
using TypeConversion = Simple.CallingAWSSDKFromLocalService.TypeConversion;
namespace simple.callingawssdkfromlocalservice.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleCallingAWSSDKFromLocalServiceClient, types._IError> WrappedSimpleCallingAWSSDKFromLocalService(types._ISimpleCallingAWSSDKFromLocalServiceConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N11_callingawssdkfromlocalservice__S23_SimpleCallingAWSSDKFromLocalServiceConfig(config);
            var impl = new SimpleCallingAWSSDKFromLocalService(wrappedConfig);
            var wrappedClient = new SimpleCallingAWSSDKFromLocalServiceShim(impl);
            return Result<types.ISimpleCallingAWSSDKFromLocalServiceClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
