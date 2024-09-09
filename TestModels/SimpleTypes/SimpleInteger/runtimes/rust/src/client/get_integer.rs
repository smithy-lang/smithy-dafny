// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetInteger`](crate::operation::get_integer::builders::GetIntegerFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::primitive::i32>>)`](crate::operation::get_integer::builders::GetIntegerFluentBuilder::value) / [`set_value(Option<::std::primitive::i32>)`](crate::operation::get_integer::builders::GetIntegerFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetIntegerOutput`](crate::operation::get_integer::GetIntegerOutput) with field(s):
    ///   - [`value(Option<::std::primitive::i32>)`](crate::operation::get_integer::GetIntegerOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetIntegerError>`](crate::operation::get_integer::GetIntegerError)
    pub fn get_integer(&self) -> crate::operation::get_integer::builders::GetIntegerFluentBuilder {
        crate::operation::get_integer::builders::GetIntegerFluentBuilder::new(self.clone())
    }
}
