// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetAggregateOutput {
    #[allow(missing_docs)] // documentation missing in model
pub nested_structure: ::std::option::Option<crate::types::NestedStructure>,
#[allow(missing_docs)] // documentation missing in model
pub simple_integer_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>,
#[allow(missing_docs)] // documentation missing in model
pub simple_string_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub simple_string_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
#[allow(missing_docs)] // documentation missing in model
pub structure_list: ::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>>,
}
impl GetAggregateOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn nested_structure(&self) -> &::std::option::Option<crate::types::NestedStructure> {
    &self.nested_structure
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_integer_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>> {
    &self.simple_integer_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.simple_string_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.simple_string_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn structure_list(&self) -> &::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>> {
    &self.structure_list
}
}
impl GetAggregateOutput {
    /// Creates a new builder-style object to manufacture [`GetAggregateOutput`](crate::operation::operation::GetAggregateOutput).
    pub fn builder() -> crate::operation::get_aggregate_known_value_test::builders::GetAggregateOutputBuilder {
        crate::operation::get_aggregate_known_value_test::builders::GetAggregateOutputBuilder::default()
    }
}

/// A builder for [`GetAggregateOutput`](crate::operation::operation::GetAggregateOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetAggregateOutputBuilder {
    pub(crate) nested_structure: ::std::option::Option<crate::types::NestedStructure>,
pub(crate) simple_integer_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>,
pub(crate) simple_string_list: ::std::option::Option<::std::vec::Vec<::std::string::String>>,
pub(crate) simple_string_map: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>,
pub(crate) structure_list: ::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>>,
}
impl GetAggregateOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn nested_structure(mut self, input: impl ::std::convert::Into<crate::types::NestedStructure>) -> Self {
    self.nested_structure = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_nested_structure(mut self, input: ::std::option::Option<crate::types::NestedStructure>) -> Self {
    self.nested_structure = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_nested_structure(&self) -> &::std::option::Option<crate::types::NestedStructure> {
    &self.nested_structure
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_integer_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>) -> Self {
    self.simple_integer_map = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_integer_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>) -> Self {
    self.simple_integer_map = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_integer_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>> {
    &self.simple_integer_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.simple_string_list = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_string_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.simple_string_list = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_string_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    &self.simple_string_list
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.simple_string_map = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_string_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.simple_string_map = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_string_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    &self.simple_string_map
}
#[allow(missing_docs)] // documentation missing in model
pub fn structure_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<crate::types::StructureListElement>>) -> Self {
    self.structure_list = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_structure_list(mut self, input: ::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>>) -> Self {
    self.structure_list = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_structure_list(&self) -> &::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>> {
    &self.structure_list
}
    /// Consumes the builder and constructs a [`GetAggregateOutput`](crate::operation::operation::GetAggregateOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_aggregate_known_value_test::GetAggregateOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_aggregate_known_value_test::GetAggregateOutput {
            nested_structure: self.nested_structure,
simple_integer_map: self.simple_integer_map,
simple_string_list: self.simple_string_list,
simple_string_map: self.simple_string_map,
structure_list: self.structure_list,
        })
    }
}
