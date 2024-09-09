// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`AlwaysNativeError`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetErrorsOutput`](crate::operation::always_native_error::GetErrorsOutput) with field(s):
    ///   - [`value(Option<::std::string::String>)`](crate::operation::always_native_error::GetErrorsOutput::value): (undocumented)
    /// - On failure, responds with [`Error`](crate::types::error::Error)
    pub fn always_native_error(&self) -> crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder {
        crate::operation::always_native_error::builders::AlwaysNativeErrorFluentBuilder::new(self.clone())
    }
}
