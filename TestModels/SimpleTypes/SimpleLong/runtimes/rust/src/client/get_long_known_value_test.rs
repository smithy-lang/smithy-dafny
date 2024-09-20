// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetLongKnownValueTest`](crate::operation::get_long_known_value_test::builders::GetLongKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::primitive::i64>>)`](crate::operation::get_long_known_value_test::builders::GetLongKnownValueTestFluentBuilder::value) / [`set_value(Option<::std::primitive::i64>)`](crate::operation::get_long_known_value_test::builders::GetLongKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetLongOutput`](crate::operation::get_long_known_value_test::GetLongOutput) with field(s):
    ///   - [`value(Option<::std::primitive::i64>)`](crate::operation::get_long_known_value_test::GetLongOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetLongKnownValueTestError>`](crate::operation::get_long_known_value_test::GetLongKnownValueTestError)
    pub fn get_long_known_value_test(&self) -> crate::operation::get_long_known_value_test::builders::GetLongKnownValueTestFluentBuilder {
        crate::operation::get_long_known_value_test::builders::GetLongKnownValueTestFluentBuilder::new(self.clone())
    }
}
