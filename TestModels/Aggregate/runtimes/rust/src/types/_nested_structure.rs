// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct NestedStructure {
    #[allow(missing_docs)] // documentation missing in model
pub string_structure: ::std::option::Option<crate::types::StringStructure>,
}
impl NestedStructure {
    #[allow(missing_docs)] // documentation missing in model
pub fn string_structure(&self) -> &::std::option::Option<crate::types::StringStructure> {
    &self.string_structure
}
}
impl NestedStructure {
    /// Creates a new builder-style object to manufacture [`NestedStructure`](crate::types::NestedStructure).
    pub fn builder() -> crate::types::builders::NestedStructureBuilder {
        crate::types::builders::NestedStructureBuilder::default()
    }
}

/// A builder for [`NestedStructure`](crate::types::NestedStructure).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct NestedStructureBuilder {
    pub(crate) string_structure: ::std::option::Option<crate::types::StringStructure>,
}
impl NestedStructureBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn string_structure(mut self, input: impl ::std::convert::Into<crate::types::StringStructure>) -> Self {
    self.string_structure = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_string_structure(mut self, input: ::std::option::Option<crate::types::StringStructure>) -> Self {
    self.string_structure = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_string_structure(&self) -> &::std::option::Option<crate::types::StringStructure> {
    &self.string_structure
}
    /// Consumes the builder and constructs a [`NestedStructure`](crate::types::NestedStructure).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::NestedStructure,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::NestedStructure {
            string_structure: self.string_structure,
        })
    }
}
