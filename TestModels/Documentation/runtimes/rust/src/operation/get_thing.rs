// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetThing`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetThing;
impl GetThing {
    /// Creates a new `GetThing`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_thing::GetThingInput,
    ) -> ::std::result::Result<
        crate::operation::get_thing::GetThingOutput,
        crate::types::error::Error,
    > {
        if input.name.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "name",
        "name was not specified but it is required when building GetThingInput",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::conversions::get_thing::_get_thing_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetThing(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_thing::_get_thing_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::get_thing::_get_thing_output::GetThingOutput;

pub use crate::operation::get_thing::_get_thing_input::GetThingInput;

pub(crate) mod _get_thing_output;

pub(crate) mod _get_thing_input;

/// Builders
pub mod builders;
