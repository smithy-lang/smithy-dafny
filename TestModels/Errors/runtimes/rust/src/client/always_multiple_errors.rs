// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`AlwaysMultipleErrors`](crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetErrorsOutput`](crate::operation::always_multiple_errors::GetErrorsOutput) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::always_multiple_errors::GetErrorsOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<AlwaysMultipleErrorsError>`](crate::operation::always_multiple_errors::AlwaysMultipleErrorsError)
    pub fn always_multiple_errors(&self) -> crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsFluentBuilder {
        crate::operation::always_multiple_errors::builders::AlwaysMultipleErrorsFluentBuilder::new(self.clone())
    }
}
