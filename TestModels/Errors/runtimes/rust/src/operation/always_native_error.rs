// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `AlwaysNativeError`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct AlwaysNativeError;
impl AlwaysNativeError {
    /// Creates a new `AlwaysNativeError`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::always_native_error::GetErrorsInput,
    ) -> ::std::result::Result<
        crate::operation::always_native_error::GetErrorsOutput,
        crate::types::error::Error,
    > {
                let inner_input = crate::conversions::always_native_error::_always_native_error_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).AlwaysNativeError(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::always_native_error::_always_native_error_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::always_native_error::_get_errors_output::GetErrorsOutput;

pub use crate::operation::always_native_error::_get_errors_input::GetErrorsInput;

pub(crate) mod _get_errors_output;

pub(crate) mod _get_errors_input;

/// Builders
pub mod builders;
