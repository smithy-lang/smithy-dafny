// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `GetResourceData`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct GetResourceData;
impl GetResourceData {
    /// Creates a new `GetResourceData`
    pub fn new() -> Self {
        Self
    }
    pub(crate) async fn send(
        simple_resource: &crate::types::simple_resource::SimpleResourceRef,
        input: crate::operation::get_resource_data::GetResourceDataInput,
    ) -> ::std::result::Result<
        crate::operation::get_resource_data::GetResourceDataOutput,
        crate::types::error::Error,
    > {
        simple_resource.inner.borrow_mut().get_resource_data(input)
    }
}

pub use crate::operation::get_resource_data::_get_resource_data_output::GetResourceDataOutput;

pub use crate::operation::get_resource_data::_get_resource_data_input::GetResourceDataInput;

pub(crate) mod _get_resource_data_output;

pub(crate) mod _get_resource_data_input;

/// Builders
pub mod builders;
