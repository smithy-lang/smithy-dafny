// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetDouble`](crate::operation::get_double::builders::GetDoubleFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::primitive::f64>>)`](crate::operation::get_double::builders::GetDoubleFluentBuilder::value) / [`set_value(Option<::std::primitive::f64>)`](crate::operation::get_double::builders::GetDoubleFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetDoubleOutput`](crate::operation::get_double::GetDoubleOutput) with field(s):
    ///   - [`value(Option<::std::primitive::f64>)`](crate::operation::get_double::GetDoubleOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetDoubleError>`](crate::operation::get_double::GetDoubleError)
    pub fn get_double(&self) -> crate::operation::get_double::builders::GetDoubleFluentBuilder {
        crate::operation::get_double::builders::GetDoubleFluentBuilder::new(self.clone())
    }
}
