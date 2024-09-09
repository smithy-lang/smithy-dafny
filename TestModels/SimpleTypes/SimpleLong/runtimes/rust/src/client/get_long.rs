// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetLong`](crate::operation::get_long::builders::GetLongFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::primitive::i64>>)`](crate::operation::get_long::builders::GetLongFluentBuilder::value) / [`set_value(Option<::std::primitive::i64>)`](crate::operation::get_long::builders::GetLongFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetLongOutput`](crate::operation::get_long::GetLongOutput) with field(s):
    ///   - [`value(Option<::std::primitive::i64>)`](crate::operation::get_long::GetLongOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetLongError>`](crate::operation::get_long::GetLongError)
    pub fn get_long(&self) -> crate::operation::get_long::builders::GetLongFluentBuilder {
        crate::operation::get_long::builders::GetLongFluentBuilder::new(self.clone())
    }
}
