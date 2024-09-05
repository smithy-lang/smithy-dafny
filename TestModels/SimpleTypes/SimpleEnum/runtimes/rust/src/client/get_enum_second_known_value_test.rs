// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetEnumSecondKnownValueTest`](crate::operation::get_enum_second_known_value_test::builders::GetEnumSecondKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<crate::types::SimpleEnumShape>>)`](crate::operation::get_enum_second_known_value_test::builders::GetEnumSecondKnownValueTestFluentBuilder::value) / [`set_value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_second_known_value_test::builders::GetEnumSecondKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetEnumOutput`](crate::operation::get_enum_second_known_value_test::GetEnumOutput) with field(s):
    ///   - [`value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_second_known_value_test::GetEnumOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetEnumSecondKnownValueTestError>`](crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError)
    pub fn get_enum_second_known_value_test(&self) -> crate::operation::get_enum_second_known_value_test::builders::GetEnumSecondKnownValueTestFluentBuilder {
        crate::operation::get_enum_second_known_value_test::builders::GetEnumSecondKnownValueTestFluentBuilder::new(self.clone())
    }
}
