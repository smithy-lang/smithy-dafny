// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetStringUTF8`](crate::operation::get_string_utf8::builders::GetStringUTF8FluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_string_utf8::builders::GetStringUTF8FluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_string_utf8::builders::GetStringUTF8FluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetStringUTF8Output`](crate::operation::get_string_utf8::GetStringUTF8Output) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::get_string_utf8::GetStringUTF8Output::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetStringUTF8Error>`](crate::operation::get_string_utf8::GetStringUTF8Error)
    pub fn get_string_utf8(&self) -> crate::operation::get_string_utf8::builders::GetStringUTF8FluentBuilder {
        crate::operation::get_string_utf8::builders::GetStringUTF8FluentBuilder::new(self.clone())
    }
}
