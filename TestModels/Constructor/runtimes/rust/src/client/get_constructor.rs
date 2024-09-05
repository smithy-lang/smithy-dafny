// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetConstructor`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_constructor::builders::GetConstructorFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetConstructorOutput`](crate::operation::get_constructor::GetConstructorOutput) with field(s):
    ///   - [`blob_value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_constructor::GetConstructorOutput::blob_value): (undocumented)
    ///   - [`boolean_value(Option<::std::primitive::bool>)`](crate::operation::get_constructor::GetConstructorOutput::boolean_value): (undocumented)
    ///   - [`integer_value(Option<::std::primitive::i32>)`](crate::operation::get_constructor::GetConstructorOutput::integer_value): (undocumented)
    ///   - [`internal_config_string(Option<::std::string::String>)`](crate::operation::get_constructor::GetConstructorOutput::internal_config_string): (undocumented)
    ///   - [`long_value(Option<::std::primitive::i64>)`](crate::operation::get_constructor::GetConstructorOutput::long_value): (undocumented)
    ///   - [`string_value(Option<::std::string::String>)`](crate::operation::get_constructor::GetConstructorOutput::string_value): (undocumented)
    /// - On failure, responds with [`SdkError<GetConstructorError>`](crate::operation::get_constructor::GetConstructorError)
    pub fn get_constructor(&self) -> crate::operation::get_constructor::builders::GetConstructorFluentBuilder {
        crate::operation::get_constructor::builders::GetConstructorFluentBuilder::new(self.clone())
    }
}
