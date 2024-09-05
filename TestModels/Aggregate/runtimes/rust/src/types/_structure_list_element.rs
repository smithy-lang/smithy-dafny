// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct StructureListElement {
    #[allow(missing_docs)] // documentation missing in model
pub integer_value: ::std::option::Option<::std::primitive::i32>,
#[allow(missing_docs)] // documentation missing in model
pub string_value: ::std::option::Option<::std::string::String>,
}
impl StructureListElement {
    #[allow(missing_docs)] // documentation missing in model
pub fn integer_value(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.integer_value
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_value(&self) -> &::std::option::Option<::std::string::String> {
    &self.string_value
}
}
impl StructureListElement {
    /// Creates a new builder-style object to manufacture [`StructureListElement`](crate::types::StructureListElement).
    pub fn builder() -> crate::types::builders::StructureListElementBuilder {
        crate::types::builders::StructureListElementBuilder::default()
    }
}

/// A builder for [`StructureListElement`](crate::types::StructureListElement).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct StructureListElementBuilder {
    pub(crate) integer_value: ::std::option::Option<::std::primitive::i32>,
pub(crate) string_value: ::std::option::Option<::std::string::String>,
}
impl StructureListElementBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn integer_value(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.integer_value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_integer_value(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.integer_value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_integer_value(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.integer_value
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_value(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.string_value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_string_value(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.string_value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_string_value(&self) -> &::std::option::Option<::std::string::String> {
    &self.string_value
}
    /// Consumes the builder and constructs a [`StructureListElement`](crate::types::StructureListElement).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::StructureListElement,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::StructureListElement {
            integer_value: self.integer_value,
string_value: self.string_value,
        })
    }
}
