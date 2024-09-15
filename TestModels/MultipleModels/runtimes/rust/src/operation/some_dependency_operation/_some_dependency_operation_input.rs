// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SomeDependencyOperationInput {

}
impl SomeDependencyOperationInput {

}
impl SomeDependencyOperationInput {
    /// Creates a new builder-style object to manufacture [`SomeDependencyOperationInput`](crate::operation::some_dependency_operation::builders::SomeDependencyOperationInput).
    pub fn builder() -> crate::operation::some_dependency_operation::builders::SomeDependencyOperationInputBuilder {
        crate::operation::some_dependency_operation::builders::SomeDependencyOperationInputBuilder::default()
    }
}

/// A builder for [`SomeDependencyOperationInput`](crate::operation::operation::SomeDependencyOperationInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SomeDependencyOperationInputBuilder {

}
impl SomeDependencyOperationInputBuilder {

    /// Consumes the builder and constructs a [`SomeDependencyOperationInput`](crate::operation::operation::SomeDependencyOperationInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::some_dependency_operation::SomeDependencyOperationInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::some_dependency_operation::SomeDependencyOperationInput {

        })
    }
}
