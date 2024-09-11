// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetConstructor`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetConstructor;
impl GetConstructor {
    /// Creates a new `GetConstructor`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_constructor::GetConstructorInput,
    ) -> ::std::result::Result<
        crate::operation::get_constructor::GetConstructorOutput,
        crate::types::error::Error,
    > {
                let inner_input = crate::conversions::get_constructor::_get_constructor_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetConstructor(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_constructor::_get_constructor_output::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::get_constructor::_get_constructor_output::GetConstructorOutput;

pub use crate::operation::get_constructor::_get_constructor_input::GetConstructorInput;

pub(crate) mod _get_constructor_output;

pub(crate) mod _get_constructor_input;

/// Builders
pub mod builders;
