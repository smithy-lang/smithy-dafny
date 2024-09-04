// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBlobInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl GetBlobInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.value
}
}
impl GetBlobInput {
    /// Creates a new builder-style object to manufacture [`GetBlobInput`](crate::operation::operation::GetBlobInput).
    pub fn builder() -> crate::operation::get_blob_known_value_test::builders::GetBlobInputBuilder {
        crate::operation::get_blob_known_value_test::builders::GetBlobInputBuilder::default()
    }
}

/// A builder for [`GetBlobInput`](crate::operation::operation::GetBlobInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBlobInputBuilder {
    pub(crate) value: ::std::option::Option<::aws_smithy_types::Blob>,
}
impl GetBlobInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetBlobInput`](crate::operation::operation::GetBlobInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_blob_known_value_test::GetBlobInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_blob_known_value_test::GetBlobInput {
            value: self.value,
        })
    }
}
