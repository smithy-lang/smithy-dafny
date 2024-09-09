// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::always_error::_get_errors_output::GetErrorsOutputBuilder;

pub use crate::operation::always_error::_get_errors_input::GetErrorsInputBuilder;

impl GetErrorsInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::always_error::GetErrorsOutput,
        crate::types::error::Error,
    > {
        let mut fluent_builder = client.always_error();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `AlwaysError`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct AlwaysErrorFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::always_error::builders::GetErrorsInputBuilder,
}
impl AlwaysErrorFluentBuilder {
    /// Creates a new `AlwaysError`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the AlwaysError as a reference.
    pub fn as_input(&self) -> &crate::operation::always_error::builders::GetErrorsInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_error::GetErrorsOutput,
        crate::types::error::Error,
    > {
        let input = self.inner.build()?;
        crate::operation::always_error::AlwaysError::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_value()
}
}
