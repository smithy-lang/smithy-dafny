// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
include "../src/WrappedSimpleExternV2Impl.dfy"
include "SimpleExternV2ImplTest.dfy"
include "WrappedSimpleExternV2ImplTest.dfy"

module {:extern "simple.dafnyexternv2.internaldafny.wrapped"} DotNamespacedWrappedSimpleExternV2Service replaces WrappedSimpleExternV2Service {}