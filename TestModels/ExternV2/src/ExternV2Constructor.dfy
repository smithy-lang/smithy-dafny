// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../Model/SimpleDafnyExternV2Types.dfy"

replaceable module ExternV2Constructor {
    import opened Wrappers
    import opened SimpleDafnyExternV2Types

    class{:extern "ExternV2ConstructorClass"} ExternV2ConstructorClass {

        function {:extern} Value(): string reads this

        // A build method is used instead of a constructor
        // because in some native runtimes, constructor can throw.
        // But Dafny constructors MUST succeed so this mismatch
        // make a static Build method required for extern classes.
        static method {:extern} Build(input: string)
        returns (output: Result<ExternV2ConstructorClass, Error>)
        ensures output.Success?
        ==>
            && output.value.Value() == input
            && fresh(output.value)

        method{:extern} GetValue() returns (output: Result<string, Error>)
    }
}
