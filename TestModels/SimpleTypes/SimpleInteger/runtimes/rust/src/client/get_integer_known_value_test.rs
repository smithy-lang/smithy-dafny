// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetIntegerKnownValueTest`](crate::operation::get_integer_known_value_test::builders::GetIntegerKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::primitive::i32>>)`](crate::operation::get_integer_known_value_test::builders::GetIntegerKnownValueTestFluentBuilder::value) / [`set_value(Option<::std::primitive::i32>)`](crate::operation::get_integer_known_value_test::builders::GetIntegerKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetIntegerOutput`](crate::operation::get_integer_known_value_test::GetIntegerOutput) with field(s):
    ///   - [`value(Option<::std::primitive::i32>)`](crate::operation::get_integer_known_value_test::GetIntegerOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetIntegerKnownValueTestError>`](crate::operation::get_integer_known_value_test::GetIntegerKnownValueTestError)
    pub fn get_integer_known_value_test(&self) -> crate::operation::get_integer_known_value_test::builders::GetIntegerKnownValueTestFluentBuilder {
        crate::operation::get_integer_known_value_test::builders::GetIntegerKnownValueTestFluentBuilder::new(self.clone())
    }
}
