// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetStringKnownValue`](crate::operation::get_string_known_value::builders::GetStringKnownValueFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_string_known_value::builders::GetStringKnownValueFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_string_known_value::builders::GetStringKnownValueFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetStringOutput`](crate::operation::get_string_known_value::GetStringOutput) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::get_string_known_value::GetStringOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetStringKnownValueError>`](crate::operation::get_string_known_value::GetStringKnownValueError)
    pub fn get_string_known_value(&self) -> crate::operation::get_string_known_value::builders::GetStringKnownValueFluentBuilder {
        crate::operation::get_string_known_value::builders::GetStringKnownValueFluentBuilder::new(self.clone())
    }
}
