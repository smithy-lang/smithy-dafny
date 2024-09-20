// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetString`](crate::operation::get_string::builders::GetStringFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_string::builders::GetStringFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_string::builders::GetStringFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetStringOutput`](crate::operation::get_string::GetStringOutput) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::get_string::GetStringOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetStringError>`](crate::operation::get_string::GetStringError)
    pub fn get_string(&self) -> crate::operation::get_string::builders::GetStringFluentBuilder {
        crate::operation::get_string::builders::GetStringFluentBuilder::new(self.clone())
    }
}
