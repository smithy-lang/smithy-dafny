// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetUnionOutput {
    #[allow(missing_docs)] // documentation missing in model
pub union: ::std::option::Option<crate::types::MyUnion>,
}
impl GetUnionOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn union(&self) -> &::std::option::Option<crate::types::MyUnion> {
    &self.union
}
}
impl GetUnionOutput {
    /// Creates a new builder-style object to manufacture [`GetUnionOutput`](crate::operation::operation::GetUnionOutput).
    pub fn builder() -> crate::operation::get_union::builders::GetUnionOutputBuilder {
        crate::operation::get_union::builders::GetUnionOutputBuilder::default()
    }
}

/// A builder for [`GetUnionOutput`](crate::operation::operation::GetUnionOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetUnionOutputBuilder {
    pub(crate) union: ::std::option::Option<crate::types::MyUnion>,
}
impl GetUnionOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn union(mut self, input: impl ::std::convert::Into<crate::types::MyUnion>) -> Self {
    self.union = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_union(mut self, input: ::std::option::Option<crate::types::MyUnion>) -> Self {
    self.union = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_union(&self) -> &::std::option::Option<crate::types::MyUnion> {
    &self.union
}
    /// Consumes the builder and constructs a [`GetUnionOutput`](crate::operation::operation::GetUnionOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_union::GetUnionOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_union::GetUnionOutput {
            union: self.union,
        })
    }
}
