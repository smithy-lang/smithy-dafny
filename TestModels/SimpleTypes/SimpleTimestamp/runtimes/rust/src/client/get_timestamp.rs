// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetTimestamp`](crate::operation::get_timestamp::builders::GetTimestampFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::aws_smithy_types::DateTime>>)`](crate::operation::get_timestamp::builders::GetTimestampFluentBuilder::value) / [`set_value(Option<::aws_smithy_types::DateTime>)`](crate::operation::get_timestamp::builders::GetTimestampFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetTimestampOutput`](crate::operation::get_timestamp::GetTimestampOutput) with field(s):
    ///   - [`value(Option<::aws_smithy_types::DateTime>)`](crate::operation::get_timestamp::GetTimestampOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetTimestampError>`](crate::operation::get_timestamp::GetTimestampError)
    pub fn get_timestamp(&self) -> crate::operation::get_timestamp::builders::GetTimestampFluentBuilder {
        crate::operation::get_timestamp::builders::GetTimestampFluentBuilder::new(self.clone())
    }
}
