// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetNameInput {
}
impl GetNameInput {
}
impl GetNameInput {
    /// Creates a new builder-style object to manufacture [`GetNameInput`](crate::operation::get_name::builders::GetNameInput).
    pub fn builder() -> crate::operation::get_name::builders::GetNameInputBuilder {
        crate::operation::get_name::builders::GetNameInputBuilder::default()
    }
}

/// A builder for [`GetNameInput`](crate::operation::operation::GetNameInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetNameInputBuilder {
}
impl GetNameInputBuilder {
    /// Consumes the builder and constructs a [`GetNameInput`](crate::operation::operation::GetNameInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_name::GetNameInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_name::GetNameInput {
        })
    }
}
