// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetResource`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetResource;
impl GetResource {
    /// Creates a new `GetResource`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_resource::GetResourceInput,
    ) -> ::std::result::Result<
        crate::operation::get_resource::GetResourceOutput,
        crate::types::error::Error,
    > {
                let inner_input = crate::conversions::get_resource::_get_resource_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetResource(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_resource::_get_resource_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::get_resource::_get_resource_output::GetResourceOutput;

pub use crate::operation::get_resource::_get_resource_input::GetResourceInput;

pub(crate) mod _get_resource_output;

pub(crate) mod _get_resource_input;

/// Builders
pub mod builders;
