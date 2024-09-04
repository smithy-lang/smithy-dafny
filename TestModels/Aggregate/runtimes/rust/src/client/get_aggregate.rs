// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetAggregate`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`nested_structure(impl Into<Option<crate::types::NestedStructure>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::nested_structure) / [`set_nested_structure(Option<crate::types::NestedStructure>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::set_nested_structure): (undocumented)<br>
    ///   - [`simple_integer_map(impl Into<Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::simple_integer_map) / [`set_simple_integer_map(Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::set_simple_integer_map): (undocumented)<br>
    ///   - [`simple_string_list(impl Into<Option<::std::vec::Vec<::std::string::String>>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::simple_string_list) / [`set_simple_string_list(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::set_simple_string_list): (undocumented)<br>
    ///   - [`simple_string_map(impl Into<Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::simple_string_map) / [`set_simple_string_map(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::set_simple_string_map): (undocumented)<br>
    ///   - [`structure_list(impl Into<Option<::std::vec::Vec<crate::types::StructureListElement>>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::structure_list) / [`set_structure_list(Option<::std::vec::Vec<crate::types::StructureListElement>>)`](crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::set_structure_list): (undocumented)<br>
    /// - On success, responds with [`GetAggregateOutput`](crate::operation::get_aggregate::GetAggregateOutput) with field(s):
    ///   - [`nested_structure(Option<crate::types::NestedStructure>)`](crate::operation::get_aggregate::GetAggregateOutput::nested_structure): (undocumented)
    ///   - [`simple_integer_map(Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>)`](crate::operation::get_aggregate::GetAggregateOutput::simple_integer_map): (undocumented)
    ///   - [`simple_string_list(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::get_aggregate::GetAggregateOutput::simple_string_list): (undocumented)
    ///   - [`simple_string_map(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::get_aggregate::GetAggregateOutput::simple_string_map): (undocumented)
    ///   - [`structure_list(Option<::std::vec::Vec<crate::types::StructureListElement>>)`](crate::operation::get_aggregate::GetAggregateOutput::structure_list): (undocumented)
    /// - On failure, responds with [`SdkError<GetAggregateError>`](crate::operation::get_aggregate::GetAggregateError)
    pub fn get_aggregate(&self) -> crate::operation::get_aggregate::builders::GetAggregateFluentBuilder {
        crate::operation::get_aggregate::builders::GetAggregateFluentBuilder::new(self.clone())
    }
}
