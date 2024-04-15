// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

// Filtering to the subset of code that Dafny Rust code generation
// currently supports.

// Only building UInt.dfy in Rust to start because other files use unsupported features
// (e.g. the variance specifiers in Option<+T>).
// This scope should be expanded over time.
include "../src/UInt.dfy"
