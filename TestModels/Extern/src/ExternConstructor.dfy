// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternTypes.dfy"

module{:extern "ExternConstructor"} ExternConstructor {
    import opened Wrappers
    import opened SimpleDafnyExternTypes

    class{:extern "ExternConstructorClass"} ExternConstructorClass {

        function {:extern} Value(): string reads this

        // A build method is used instead of a constructor
        // because in some native runtimes, constructor can throw.
        // But Dafny constructors MUST succeed so this mismatch
        // make a static Build method required for extern classes.
        static method {:extern} Build(input: string)
        returns (output: Result<ExternConstructorClass, Error>)
        ensures output.Success?
        ==>
            && output.value.Value() == input
            && fresh(output.value)

        method{:extern} GetValue() returns (output: Result<string, Error>)
    }
}
