// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetEnumFirstKnownValueTest`](crate::operation::get_enum_first_known_value_test::builders::GetEnumFirstKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<crate::types::SimpleEnumShape>>)`](crate::operation::get_enum_first_known_value_test::builders::GetEnumFirstKnownValueTestFluentBuilder::value) / [`set_value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_first_known_value_test::builders::GetEnumFirstKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetEnumOutput`](crate::operation::get_enum_first_known_value_test::GetEnumOutput) with field(s):
    ///   - [`value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_first_known_value_test::GetEnumOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetEnumFirstKnownValueTestError>`](crate::operation::get_enum_first_known_value_test::GetEnumFirstKnownValueTestError)
    pub fn get_enum_first_known_value_test(&self) -> crate::operation::get_enum_first_known_value_test::builders::GetEnumFirstKnownValueTestFluentBuilder {
        crate::operation::get_enum_first_known_value_test::builders::GetEnumFirstKnownValueTestFluentBuilder::new(self.clone())
    }
}
