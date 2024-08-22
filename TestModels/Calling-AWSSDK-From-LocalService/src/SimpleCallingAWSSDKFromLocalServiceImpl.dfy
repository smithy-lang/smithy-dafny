// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleCallingawssdkfromlocalserviceTypes.dfy"

module SimpleCallingAWSSDKFromLocalServiceImpl refines AbstractSimpleCallingawssdkfromlocalserviceOperations  {
    datatype Config = Config
    type InternalConfig = Config
    predicate ValidInternalConfig?(config: InternalConfig)
    {true}
    function ModifiesInternalConfig(config: InternalConfig) : set<object>
    {{}}
    predicate CallDDBEnsuresPublicly(input: CallDDBInput, output: Result<CallDDBOutput, Error>) {
        true
    }

    method CallDDB ( config: InternalConfig,  input: CallDDBInput )
    returns (output: Result<CallDDBOutput, Error>) {
        var res := CallDDBOutput(tableArn := "input.value");
        print(res);
        return Success(res);
    }
}