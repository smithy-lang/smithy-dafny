// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetKnownValueUnionInput {
    #[allow(missing_docs)] // documentation missing in model
pub union: ::std::option::Option<crate::types::KnownValueUnion>,
}
impl GetKnownValueUnionInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn union(&self) -> &::std::option::Option<crate::types::KnownValueUnion> {
    &self.union
}
}
impl GetKnownValueUnionInput {
    /// Creates a new builder-style object to manufacture [`GetKnownValueUnionInput`](crate::operation::operation::GetKnownValueUnionInput).
    pub fn builder() -> crate::operation::get_known_value_union::builders::GetKnownValueUnionInputBuilder {
        crate::operation::get_known_value_union::builders::GetKnownValueUnionInputBuilder::default()
    }
}

/// A builder for [`GetKnownValueUnionInput`](crate::operation::operation::GetKnownValueUnionInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetKnownValueUnionInputBuilder {
    pub(crate) union: ::std::option::Option<crate::types::KnownValueUnion>,
}
impl GetKnownValueUnionInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn union(mut self, input: impl ::std::convert::Into<crate::types::KnownValueUnion>) -> Self {
    self.union = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_union(mut self, input: ::std::option::Option<crate::types::KnownValueUnion>) -> Self {
    self.union = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_union(&self) -> &::std::option::Option<crate::types::KnownValueUnion> {
    &self.union
}
    /// Consumes the builder and constructs a [`GetKnownValueUnionInput`](crate::operation::operation::GetKnownValueUnionInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_known_value_union::GetKnownValueUnionInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_known_value_union::GetKnownValueUnionInput {
            union: self.union,
        })
    }
}
