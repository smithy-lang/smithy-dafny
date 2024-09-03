// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetEnum`](crate::operation::get_enum::builders::GetEnumFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<crate::types::SimpleEnumShape>>)`](crate::operation::get_enum::builders::GetEnumFluentBuilder::value) / [`set_value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum::builders::GetEnumFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetEnumOutput`](crate::operation::get_enum::GetEnumOutput) with field(s):
    ///   - [`value(Option<crate::types::SimpleEnumShape>)`](crate::operation::get_enum::GetEnumOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetEnumError>`](crate::operation::get_enum::GetEnumError)
    pub fn get_enum(&self) -> crate::operation::get_enum::builders::GetEnumFluentBuilder {
        crate::operation::get_enum::builders::GetEnumFluentBuilder::new(self.clone())
    }
}
