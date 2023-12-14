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
module {:extern "simple.dafnyexternv2.internaldafny"} JavaSimpleExternV2 replaces SimpleExternV2 {

    // Here, you might write some code that would ONLY be compiled to Java.
    // For the sake of demonstration, let's say we don't need to write any code here.
    // However, since `DotNamespacedSimpleExternV2` is marked `replaceable` to allow
    //   our `IndexNet.dfy` to write some code here,
    //   we need to `replace` the `replaceable` module at some point in the program.
    // This file exists to replace the module.
}