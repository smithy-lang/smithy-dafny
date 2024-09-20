// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetEnumThirdKnownValueTest`](crate::operation::get_enum_third_known_value_test::builders::GetEnumThirdKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<crate::types::SimpleEnumShape>>)`](crate::operation::get_enum_third_known_value_test::builders::GetEnumThirdKnownValueTestFluentBuilder::value) / [`set_value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_third_known_value_test::builders::GetEnumThirdKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetEnumOutput`](crate::operation::get_enum_third_known_value_test::GetEnumOutput) with field(s):
    ///   - [`value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum_third_known_value_test::GetEnumOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetEnumThirdKnownValueTestError>`](crate::operation::get_enum_third_known_value_test::GetEnumThirdKnownValueTestError)
    pub fn get_enum_third_known_value_test(&self) -> crate::operation::get_enum_third_known_value_test::builders::GetEnumThirdKnownValueTestFluentBuilder {
        crate::operation::get_enum_third_known_value_test::builders::GetEnumThirdKnownValueTestFluentBuilder::new(self.clone())
    }
}
