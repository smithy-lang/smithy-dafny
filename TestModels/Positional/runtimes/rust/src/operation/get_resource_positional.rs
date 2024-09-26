// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetResourcePositional`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetResourcePositional;
impl GetResourcePositional {
    /// Creates a new `GetResourcePositional`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_resource_positional::GetResourcePositionalInput,
    ) -> ::std::result::Result<
        crate::types::simple_resource::SimpleResourceRef,
        crate::types::error::Error,
    > {
        if input.name.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "name",
        "name was not specified but it is required when building GetResourcePositionalInput",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::standard_library_conversions::ostring_to_dafny(&input.name) .Extract();
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetResourcePositional(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::simple_resource::from_dafny(inner_result.value().clone())
,
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::get_resource_positional::_get_resource_positional_output::GetResourcePositionalOutput;

pub use crate::operation::get_resource_positional::_get_resource_positional_input::GetResourcePositionalInput;

pub(crate) mod _get_resource_positional_output;

pub(crate) mod _get_resource_positional_input;

/// Builders
pub mod builders;
