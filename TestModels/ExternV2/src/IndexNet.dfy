// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Include any extern definitions shared between all `.`-namespaced languages
include "IndexDotNamespaced.dfy"

// Note that even though `JavaSimpleExternV2` and `NetSimpleExternV2` share the same `extern` name,
//   we cannot define that in `IndexDotNamespaced.dfy` and `replace` it from these files.
// `replace`ing a module removes any `extern` attributes from it.
// These files would need to redefine the `extern` name even if it was defined in IndexDotNamespaced.
// If the .NET extern did not have language-specific behavior, we could move this `extern`
//   definition into IndexDotNamespaced.
module {:extern "simple.dafnyexternv2.internaldafny"} NetSimpleExternV2 replaces SimpleExternV2 {

    // For the sake of example, assume that this module has some language-specific behavior.
    // In this file, you might write some code that would ONLY be compiled to .NET.
    // By writing some of this language-specific behavior in Dafny,
    //   you can verify part of the extern's behavior in Dafny via `requires`/`modifies`/`ensures`
    //   and narrow down the amount of unverified code in extern modules.

    method {:extern "ExampleOnlyNet"} OnlyNetMethodExample(input: string)
        // Note: No need to `import opened Wrappers` for `Result`; it is included from `SimpleExternV2`.
        returns (output: Result<string, Error>)
        ensures output.Success?
        ==>
            && output.value == input

    // We can also write some glue code that calls this extern, and validate that
    // the glue code is verified by Dafny.
    method CallOnlyNetMethod(input: string) returns (output: string)
        ensures output == input
    {
        var externOutput :- expect OnlyNetMethodExample(input);
        return externOutput;
    }

}
