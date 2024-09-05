// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetBlob`](crate::operation::get_blob::builders::GetBlobFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::aws_smithy_types::Blob>>)`](crate::operation::get_blob::builders::GetBlobFluentBuilder::value) / [`set_value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_blob::builders::GetBlobFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetBlobOutput`](crate::operation::get_blob::GetBlobOutput) with field(s):
    ///   - [`value(Option<::aws_smithy_types::Blob>)`](crate::operation::get_blob::GetBlobOutput::value): (undocumented)
    /// - On failure, responds with [`SdkError<GetBlobError>`](crate::operation::get_blob::GetBlobError)
    pub fn get_blob(&self) -> crate::operation::get_blob::builders::GetBlobFluentBuilder {
        crate::operation::get_blob::builders::GetBlobFluentBuilder::new(self.clone())
    }
}
