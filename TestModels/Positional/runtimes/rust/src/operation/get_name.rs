// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetName`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetName;
impl GetName {
    /// Creates a new `GetName`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        simple_resource: &crate::types::simple_resource::SimpleResourceRef,
        input: crate::operation::get_name::GetNameInput,
    ) -> ::std::result::Result<
        crate::operation::get_name::GetNameOutput,
        crate::types::error::Error,
    > {

        simple_resource.inner.borrow_mut().get_name(input)
    }
}

pub use crate::operation::get_name::_get_name_output::GetNameOutput;

pub use crate::operation::get_name::_get_name_input::GetNameInput;

pub(crate) mod _get_name_output;

pub(crate) mod _get_name_input;

/// Builders
pub mod builders;
