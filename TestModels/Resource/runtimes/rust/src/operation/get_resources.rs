// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetResources`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetResources;
impl GetResources {
    /// Creates a new `GetResources`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_resources::GetResourcesInput,
    ) -> ::std::result::Result<
        crate::operation::get_resources::GetResourcesOutput,
        crate::types::error::Error,
    > {
                let inner_input = crate::conversions::get_resources::_get_resources_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetResources(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_resources::_get_resources_output::from_dafny(
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

pub use crate::operation::get_resources::_get_resources_output::GetResourcesOutput;

pub use crate::operation::get_resources::_get_resources_input::GetResourcesInput;

pub(crate) mod _get_resources_output;

pub(crate) mod _get_resources_input;

/// Builders
pub mod builders;
