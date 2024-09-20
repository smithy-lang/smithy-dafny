// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetStringUTF8KnownValue`](crate::operation::get_string_utf8_known_value::builders::GetStringUTF8KnownValueFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_string_utf8_known_value::builders::GetStringUTF8KnownValueFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_string_utf8_known_value::builders::GetStringUTF8KnownValueFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetStringUTF8Output`](crate::operation::get_string_utf8_known_value::GetStringUTF8Output) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::get_string_utf8_known_value::GetStringUTF8Output::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetStringUTF8KnownValueError>`](crate::operation::get_string_utf8_known_value::GetStringUTF8KnownValueError)
    pub fn get_string_utf8_known_value(&self) -> crate::operation::get_string_utf8_known_value::builders::GetStringUTF8KnownValueFluentBuilder {
        crate::operation::get_string_utf8_known_value::builders::GetStringUTF8KnownValueFluentBuilder::new(self.clone())
    }
}
