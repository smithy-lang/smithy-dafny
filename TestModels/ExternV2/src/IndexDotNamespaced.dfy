// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "Index.dfy"

module {:extern "simple.dafnyexternv2.internaldafny.ExternV2Constructor"} DotNamespacedExternV2Constructor replaces ExternV2Constructor {
    // For the sake of example, assume we do not have per-language behavior for this module.
    // Then, we can define it in a `DotNamespaced` module.
    // Languages that use `.`-namespacing can include this file from their language-specifix Index files
    // to share the module extern definition.
}

// Note that even though `JavaSimpleExternV2` and `NetSimpleExternV2` share the same `extern` name,
//   we cannot define that here and `replace` it from those files.
// `replace`ing a module removes any `extern` attributes from it.
// Those files would need to redefine the `extern` name even if it was defined in this file.
// If the .NET extern did not have language-specific behavior, we could move that `extern`
//   definition into this file.