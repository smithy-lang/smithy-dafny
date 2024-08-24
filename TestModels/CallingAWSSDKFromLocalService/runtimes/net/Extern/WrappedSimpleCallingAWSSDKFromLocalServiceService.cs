// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
using Wrappers_Compile;
using Simple.Callingawssdkfromlocalservice;
using Simple.Callingawssdkfromlocalservice.Wrapped;
using TypeConversion = Simple.Callingawssdkfromlocalservice.TypeConversion;
namespace simple.callingawssdkfromlocalservice.internaldafny.wrapped
{
    public partial class __default
    {
        public static _IResult<types.ISimpleCallingAWSSDKFromLocalServiceClient, types._IError> WrappedSimpleCallingAWSSDKFromLocalService(types._ISimpleCallingAWSSDKFromLocalServiceConfig config)
        {
            var wrappedConfig = TypeConversion.FromDafny_N6_simple__N29_callingawssdkfromlocalservice__S41_SimpleCallingAWSSDKFromLocalServiceConfig(config);
            var impl = new SimpleCallingAWSSDKFromLocalService(wrappedConfig);
            var wrappedClient = new SimpleCallingAWSSDKFromLocalServiceShim(impl);
            return Result<types.ISimpleCallingAWSSDKFromLocalServiceClient, types._IError>.create_Success(wrappedClient);
        }
    }
}
