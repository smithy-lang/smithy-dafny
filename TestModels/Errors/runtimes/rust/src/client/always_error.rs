// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`AlwaysError`](crate::operation::always_error::builders::AlwaysErrorFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::always_error::builders::AlwaysErrorFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::always_error::builders::AlwaysErrorFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetErrorsOutput`](crate::operation::always_error::GetErrorsOutput) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::always_error::GetErrorsOutput::value): (undocumented)
    /// - On failure, responds with [`Error`](crate::types::error::Error)
    pub fn always_error(&self) -> crate::operation::always_error::builders::AlwaysErrorFluentBuilder {
        crate::operation::always_error::builders::AlwaysErrorFluentBuilder::new(self.clone())
    }
}
