// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetEnumV2SecondKnownValueTest`](crate::operation::get_enum_v2_second_known_value_test::builders::GetEnumV2SecondKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<crate::types::SimpleEnumV2Shape>>)`](crate::operation::get_enum_v2_second_known_value_test::builders::GetEnumV2SecondKnownValueTestFluentBuilder::value) / [`set_value(Option<crate::types::SimpleEnumV2Shape>)`](crate::operation::get_enum_v2_second_known_value_test::builders::GetEnumV2SecondKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetEnumV2Output`](crate::operation::get_enum_v2_second_known_value_test::GetEnumV2Output) with field(s):
    ///   - [`value(Option<crate::types::SimpleEnumV2Shape>)`](crate::operation::get_enum_v2_second_known_value_test::GetEnumV2Output::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetEnumV2SecondKnownValueTestError>`](crate::operation::get_enum_v2_second_known_value_test::GetEnumV2SecondKnownValueTestError)
    pub fn get_enum_v2_second_known_value_test(&self) -> crate::operation::get_enum_v2_second_known_value_test::builders::GetEnumV2SecondKnownValueTestFluentBuilder {
        crate::operation::get_enum_v2_second_known_value_test::builders::GetEnumV2SecondKnownValueTestFluentBuilder::new(self.clone())
    }
}
