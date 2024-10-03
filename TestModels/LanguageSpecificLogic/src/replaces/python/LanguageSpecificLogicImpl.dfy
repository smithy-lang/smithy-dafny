// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../../LanguageSpecificLogicImpl.dfy"

module PythonLanguageSpecificLogicImpl replaces LanguageSpecificLogicImpl  {
    // This method is listed as an operation on the service in the Smithy model.
    // Smithy-Dafny will write code to call this operation.
    // Internally, the generated Dafny will call the extern.
    // This provides a consistent interface for users.
    method GetRuntimeInformation(config: InternalConfig)
        returns (output: Result<GetRuntimeInformationOutput, Error>)
        ensures output.Success? ==>
            && output.value.language == "Python"
            && output.value.runtime != ""
    {
        var runtimeInfo :- expect GetRuntimeInformationPythonExternMethod(config);
        var getRuntimeInformationOutput := GetRuntimeInformationOutput(
            language := "Python",
            runtime := runtimeInfo
        );
        return Success(getRuntimeInformationOutput);
    }

    // This method is NOT listed as an operation on the service in the Smithy model.
    // Since this is an extern method with a different name per language, we can't define
    //   the interface for this method on the Smithy model.
    // Instead, we define the `AllRuntimesMethod` which IS a Smithy operation
    //   and call this method from there.
    method {:extern "GetPythonRuntimeVersion" } GetRuntimeInformationPythonExternMethod(config: InternalConfig)
        returns (output: Result<string, Error>)
        ensures output.Success? ==> output.value != ""
}
