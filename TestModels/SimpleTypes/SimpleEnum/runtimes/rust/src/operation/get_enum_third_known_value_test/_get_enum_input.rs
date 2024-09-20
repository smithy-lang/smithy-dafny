// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetEnumInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<crate::types::SimpleEnumShape>,
}
impl GetEnumInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<crate::types::SimpleEnumShape> {
    self.value.clone()
}
}
impl GetEnumInput {
    /// Creates a new builder-style object to manufacture [`GetEnumInput`](crate::operation::operation::GetEnumInput).
    pub fn builder() -> crate::operation::get_enum_third_known_value_test::builders::GetEnumInputBuilder {
        crate::operation::get_enum_third_known_value_test::builders::GetEnumInputBuilder::default()
    }
}

/// A builder for [`GetEnumInput`](crate::operation::operation::GetEnumInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetEnumInputBuilder {
    pub(crate) value: ::std::option::Option<crate::types::SimpleEnumShape>,
}
impl GetEnumInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<crate::types::SimpleEnumShape>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<crate::types::SimpleEnumShape>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<crate::types::SimpleEnumShape> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetEnumInput`](crate::operation::operation::GetEnumInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_enum_third_known_value_test::GetEnumInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_enum_third_known_value_test::GetEnumInput {
            value: self.value,
        })
    }
}
