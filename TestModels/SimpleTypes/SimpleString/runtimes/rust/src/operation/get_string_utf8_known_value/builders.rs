// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_string_utf8_known_value::_get_string_utf8_output::GetStringUtf8OutputBuilder;

pub use crate::operation::get_string_utf8_known_value::_get_string_utf8_input::GetStringUtf8InputBuilder;

impl GetStringUtf8InputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8_known_value::GetStringUtf8Output,
        crate::operation::get_string_utf8_known_value::GetStringUtf8KnownValueError,
    > {
        let mut fluent_builder = client.get_string_utf8_known_value();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetStringUtf8KnownValue`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetStringUtf8KnownValueFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_string_utf8_known_value::builders::GetStringUtf8InputBuilder,
}
impl GetStringUtf8KnownValueFluentBuilder {
    /// Creates a new `GetStringUtf8KnownValue`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetStringUtf8KnownValue as a reference.
    pub fn as_input(&self) -> &crate::operation::get_string_utf8_known_value::builders::GetStringUtf8InputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8_known_value::GetStringUtf8Output,
        crate::operation::get_string_utf8_known_value::GetStringUtf8KnownValueError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetStringUtf8KnownValue doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_string_utf8_known_value::GetStringUtf8KnownValueError::unhandled)?;
        crate::operation::get_string_utf8_known_value::GetStringUtf8KnownValue::send(&self.client, input).await
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
