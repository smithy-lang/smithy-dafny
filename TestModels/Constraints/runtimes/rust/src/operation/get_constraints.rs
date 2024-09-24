// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetConstraints`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetConstraints;
impl GetConstraints {
    /// Creates a new `GetConstraints`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::client::Client,
        input: crate::operation::get_constraints::GetConstraintsInput,
    ) -> ::std::result::Result<
        crate::operation::get_constraints::GetConstraintsOutput,
        crate::types::error::Error,
    > {
        if matches!(input.my_string, Some(ref x) if !(1..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_string",
        "my_string failed to satisfy constraint: Member must have length between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.non_empty_string, Some(ref x) if !(1..).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "non_empty_string",
        "non_empty_string failed to satisfy constraint: Member must have length greater than or equal to 1",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.string_less_than_or_equal_to_ten, Some(ref x) if !(..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "string_less_than_or_equal_to_ten",
        "string_less_than_or_equal_to_ten failed to satisfy constraint: Member must have length less than or equal to 10",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_blob, Some(ref x) if !(1..=10).contains(&x.as_ref().len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_blob",
        "my_blob failed to satisfy constraint: Member must have length between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.non_empty_blob, Some(ref x) if !(1..).contains(&x.as_ref().len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "non_empty_blob",
        "non_empty_blob failed to satisfy constraint: Member must have length greater than or equal to 1",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.blob_less_than_or_equal_to_ten, Some(ref x) if !(..=10).contains(&x.as_ref().len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "blob_less_than_or_equal_to_ten",
        "blob_less_than_or_equal_to_ten failed to satisfy constraint: Member must have length less than or equal to 10",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_list, Some(ref x) if !(1..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_list",
        "my_list failed to satisfy constraint: Member must have length between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.non_empty_list, Some(ref x) if !(1..).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "non_empty_list",
        "non_empty_list failed to satisfy constraint: Member must have length greater than or equal to 1",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.list_less_than_or_equal_to_ten, Some(ref x) if !(..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "list_less_than_or_equal_to_ten",
        "list_less_than_or_equal_to_ten failed to satisfy constraint: Member must have length less than or equal to 10",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_map, Some(ref x) if !(1..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_map",
        "my_map failed to satisfy constraint: Member must have length between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.non_empty_map, Some(ref x) if !(1..).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "non_empty_map",
        "non_empty_map failed to satisfy constraint: Member must have length greater than or equal to 1",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.map_less_than_or_equal_to_ten, Some(ref x) if !(..=10).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "map_less_than_or_equal_to_ten",
        "map_less_than_or_equal_to_ten failed to satisfy constraint: Member must have length less than or equal to 10",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.one_to_ten, Some(x) if !(1..=10).contains(&x)) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "one_to_ten",
        "one_to_ten failed to satisfy constraint: Member must be between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_ten_to_ten, Some(x) if !(-10..=10).contains(&x)) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_ten_to_ten",
        "my_ten_to_ten failed to satisfy constraint: Member must be between -10 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.greater_than_one, Some(x) if !(1..).contains(&x)) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "greater_than_one",
        "greater_than_one failed to satisfy constraint: Member must be greater than or equal to 1",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.less_than_ten, Some(x) if !(..=10).contains(&x)) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "less_than_ten",
        "less_than_ten failed to satisfy constraint: Member must be less than or equal to 10",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_utf8_bytes, Some(ref x) if !(1..=10).contains(&x.chars().count())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_utf8_bytes",
        "my_utf8_bytes failed to satisfy constraint: Member must have length between 1 and 10, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
if matches!(input.my_list_of_utf8_bytes, Some(ref x) if !(1..=2).contains(&x.len())) {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
        "my_list_of_utf8_bytes",
        "my_list_of_utf8_bytes failed to satisfy constraint: Member must have length between 1 and 2, inclusive",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
                let inner_input = crate::conversions::get_constraints::_get_constraints_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).GetConstraints(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_constraints::_get_constraints_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::operation::get_constraints::_get_constraints_output::GetConstraintsOutput;

pub use crate::operation::get_constraints::_get_constraints_input::GetConstraintsInput;

pub(crate) mod _get_constraints_output;

pub(crate) mod _get_constraints_input;

/// Builders
pub mod builders;
