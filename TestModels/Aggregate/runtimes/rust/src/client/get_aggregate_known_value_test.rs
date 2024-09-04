// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetAggregateKnownValueTest`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`nested_structure(impl Into<Option<crate::types::NestedStructure>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::nested_structure) / [`set_nested_structure(Option<crate::types::NestedStructure>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::set_nested_structure): (undocumented)<br>
    ///   - [`simple_integer_map(impl Into<Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::simple_integer_map) / [`set_simple_integer_map(Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::set_simple_integer_map): (undocumented)<br>
    ///   - [`simple_string_list(impl Into<Option<::std::vec::Vec<::std::string::String>>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::simple_string_list) / [`set_simple_string_list(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::set_simple_string_list): (undocumented)<br>
    ///   - [`simple_string_map(impl Into<Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::simple_string_map) / [`set_simple_string_map(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::set_simple_string_map): (undocumented)<br>
    ///   - [`structure_list(impl Into<Option<::std::vec::Vec<crate::types::StructureListElement>>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::structure_list) / [`set_structure_list(Option<::std::vec::Vec<crate::types::StructureListElement>>)`](crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::set_structure_list): (undocumented)<br>
    /// - On success, responds with [`GetAggregateOutput`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput) with field(s):
    ///   - [`nested_structure(Option<crate::types::NestedStructure>)`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput::nested_structure): (undocumented)
    ///   - [`simple_integer_map(Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>)`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput::simple_integer_map): (undocumented)
    ///   - [`simple_string_list(Option<::std::vec::Vec<::std::string::String>>)`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput::simple_string_list): (undocumented)
    ///   - [`simple_string_map(Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>)`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput::simple_string_map): (undocumented)
    ///   - [`structure_list(Option<::std::vec::Vec<crate::types::StructureListElement>>)`](crate::operation::get_aggregate_known_value_test::GetAggregateOutput::structure_list): (undocumented)
    /// - On failure, responds with [`SdkError<GetAggregateKnownValueTestError>`](crate::operation::get_aggregate_known_value_test::GetAggregateKnownValueTestError)
    pub fn get_aggregate_known_value_test(&self) -> crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder {
        crate::operation::get_aggregate_known_value_test::builders::GetAggregateKnownValueTestFluentBuilder::new(self.clone())
    }
}
