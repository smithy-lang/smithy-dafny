// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SomePrimaryOperationInput {

}
impl SomePrimaryOperationInput {

}
impl SomePrimaryOperationInput {
    /// Creates a new builder-style object to manufacture [`SomePrimaryOperationInput`](crate::operation::some_primary_operation::builders::SomePrimaryOperationInput).
    pub fn builder() -> crate::operation::some_primary_operation::builders::SomePrimaryOperationInputBuilder {
        crate::operation::some_primary_operation::builders::SomePrimaryOperationInputBuilder::default()
    }
}

/// A builder for [`SomePrimaryOperationInput`](crate::operation::operation::SomePrimaryOperationInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SomePrimaryOperationInputBuilder {

}
impl SomePrimaryOperationInputBuilder {

    /// Consumes the builder and constructs a [`SomePrimaryOperationInput`](crate::operation::operation::SomePrimaryOperationInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::some_primary_operation::SomePrimaryOperationInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::some_primary_operation::SomePrimaryOperationInput {

        })
    }
}
