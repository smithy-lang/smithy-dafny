// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `SomePrimaryOperation`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct SomePrimaryOperation;
impl SomePrimaryOperation {
    /// Creates a new `SomePrimaryOperation`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::some_primary_operation::SomePrimaryOperationInput,
    ) -> ::std::result::Result<
        crate::operation::some_primary_operation::SomePrimaryOperationOutput,
        crate::types::error::Error,
    > {
                let inner_input = crate::conversions::some_primary_operation::_some_primary_operation_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).SomePrimaryOperation(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::some_primary_operation::_some_primary_operation_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::some_primary_operation::_some_primary_operation_output::SomePrimaryOperationOutput;

pub use crate::operation::some_primary_operation::_some_primary_operation_input::SomePrimaryOperationInput;

pub(crate) mod _some_primary_operation_output;

pub(crate) mod _some_primary_operation_input;

/// Builders
pub mod builders;
