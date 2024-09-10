// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::types::simple_resource::SimpleResourceRef {
    /// Constructs a fluent builder for the [`GetResourceData`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`blob_value(impl Into<Option<::aws_smithy_types::Blob>>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::blob_value) / [`set_blob_value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::set_blob_value): (undocumented)<br>
    ///   - [`boolean_value(impl Into<Option<::std::primitive::bool>>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::boolean_value) / [`set_boolean_value(Option<::std::primitive::bool>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::set_boolean_value): (undocumented)<br>
    ///   - [`integer_value(impl Into<Option<::std::primitive::i32>>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::integer_value) / [`set_integer_value(Option<::std::primitive::i32>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::set_integer_value): (undocumented)<br>
    ///   - [`long_value(impl Into<Option<::std::primitive::i64>>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::long_value) / [`set_long_value(Option<::std::primitive::i64>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::set_long_value): (undocumented)<br>
    ///   - [`string_value(impl Into<Option<::std::string::String>>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::string_value) / [`set_string_value(Option<::std::string::String>)`](crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::set_string_value): (undocumented)<br>
    /// - On success, responds with [`GetResourceDataOutput`](crate::operation::get_resource_data::GetResourceDataOutput) with field(s):
    ///   - [`blob_value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_resource_data::GetResourceDataOutput::blob_value): (undocumented)
    ///   - [`boolean_value(Option<::std::primitive::bool>)`](crate::operation::get_resource_data::GetResourceDataOutput::boolean_value): (undocumented)
    ///   - [`integer_value(Option<::std::primitive::i32>)`](crate::operation::get_resource_data::GetResourceDataOutput::integer_value): (undocumented)
    ///   - [`long_value(Option<::std::primitive::i64>)`](crate::operation::get_resource_data::GetResourceDataOutput::long_value): (undocumented)
    ///   - [`string_value(Option<::std::string::String>)`](crate::operation::get_resource_data::GetResourceDataOutput::string_value): (undocumented)
    /// - On failure, responds with [`SdkError<GetResourceDataError>`](crate::operation::get_resource_data::GetResourceDataError)
    pub fn get_resource_data(&self) -> crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder {
        crate::operation::get_resource_data::builders::GetResourceDataFluentBuilder::new(self.clone())
    }
}
