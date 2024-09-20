// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetBlobKnownValueTest`](crate::operation::get_blob_known_value_test::builders::GetBlobKnownValueTestFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::aws_smithy_types::Blob>>)`](crate::operation::get_blob_known_value_test::builders::GetBlobKnownValueTestFluentBuilder::value) / [`set_value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_blob_known_value_test::builders::GetBlobKnownValueTestFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetBlobOutput`](crate::operation::get_blob_known_value_test::GetBlobOutput) with field(s):
    ///   - [`value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_blob_known_value_test::GetBlobOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetBlobKnownValueTestError>`](crate::operation::get_blob_known_value_test::GetBlobKnownValueTestError)
    pub fn get_blob_known_value_test(&self) -> crate::operation::get_blob_known_value_test::builders::GetBlobKnownValueTestFluentBuilder {
        crate::operation::get_blob_known_value_test::builders::GetBlobKnownValueTestFluentBuilder::new(self.clone())
    }
}
