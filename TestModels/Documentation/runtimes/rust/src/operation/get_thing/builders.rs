// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_thing::_get_thing_output::GetThingOutputBuilder;

pub use crate::operation::get_thing::_get_thing_input::GetThingInputBuilder;

impl GetThingInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::client::Client,
    ) -> ::std::result::Result<
        crate::operation::get_thing::GetThingOutput,
        crate::types::error::Error,
    > {
        let mut fluent_builder = client.get_thing();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetThing`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetThingFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_thing::builders::GetThingInputBuilder,
}
impl GetThingFluentBuilder {
    /// Creates a new `GetThing`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetThing as a reference.
    pub fn as_input(&self) -> &crate::operation::get_thing::builders::GetThingInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_thing::GetThingOutput,
        crate::types::error::Error,
    > {
        let input = self
            .inner
            .build()
            // Using Opaque since we don't have a validation-specific error yet.
            // Operations' models don't declare their own validation error,
            // and smithy-rs seems to not generate a ValidationError case unless there is.
            // Vanilla smithy-rs uses SdkError::construction_failure, but we aren't using SdkError.
            .map_err(|mut e| crate::types::error::Error::Opaque {
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any),
		alt_text : format!("{:?}", e)
            })?;
        crate::operation::get_thing::GetThing::send(&self.client, input).await
    }

    /// The name of the thing to get, obviously.
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.name(input.into());
    self
}
/// The name of the thing to get, obviously.
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_name(input);
    self
}
/// The name of the thing to get, obviously.
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_name()
}
}
