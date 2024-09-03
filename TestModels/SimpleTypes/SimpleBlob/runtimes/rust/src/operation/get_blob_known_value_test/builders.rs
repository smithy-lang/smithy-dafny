// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_blob_known_value_test::_get_blob_output::GetBlobOutputBuilder;

pub use crate::operation::get_blob_known_value_test::_get_blob_input::GetBlobInputBuilder;

impl GetBlobInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_blob_known_value_test::GetBlobOutput,
        crate::operation::get_blob_known_value_test::GetBlobKnownValueTestError,
    > {
        let mut fluent_builder = client.get_blob_known_value_test();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetBlobKnownValueTest`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetBlobKnownValueTestFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_blob_known_value_test::builders::GetBlobInputBuilder,
}
impl GetBlobKnownValueTestFluentBuilder {
    /// Creates a new `GetBlobKnownValueTest`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetBlobKnownValueTest as a reference.
    pub fn as_input(&self) -> &crate::operation::get_blob_known_value_test::builders::GetBlobInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_blob_known_value_test::GetBlobOutput,
        crate::operation::get_blob_known_value_test::GetBlobKnownValueTestError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetBlobKnownValueTest doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_blob_known_value_test::GetBlobKnownValueTestError::unhandled)?;
        crate::operation::get_blob_known_value_test::GetBlobKnownValueTest::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_value()
}
}
