// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_known_value_union::_get_known_value_union_output::GetKnownValueUnionOutputBuilder;

pub use crate::operation::get_known_value_union::_get_known_value_union_input::GetKnownValueUnionInputBuilder;

impl GetKnownValueUnionInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_known_value_union::GetKnownValueUnionOutput,
        crate::operation::get_known_value_union::GetKnownValueUnionError,
    > {
        let mut fluent_builder = client.get_known_value_union();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetKnownValueUnion`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetKnownValueUnionFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_known_value_union::builders::GetKnownValueUnionInputBuilder,
}
impl GetKnownValueUnionFluentBuilder {
    /// Creates a new `GetKnownValueUnion`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetKnownValueUnion as a reference.
    pub fn as_input(&self) -> &crate::operation::get_known_value_union::builders::GetKnownValueUnionInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_known_value_union::GetKnownValueUnionOutput,
        crate::operation::get_known_value_union::GetKnownValueUnionError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetKnownValueUnion doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_known_value_union::GetKnownValueUnionError::unhandled)?;
        crate::operation::get_known_value_union::GetKnownValueUnion::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn union(mut self, input: impl ::std::convert::Into<crate::types::KnownValueUnion>) -> Self {
    self.inner = self.inner.union(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_union(mut self, input: ::std::option::Option<crate::types::KnownValueUnion>) -> Self {
    self.inner = self.inner.set_union(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_union(&self) -> &::std::option::Option<crate::types::KnownValueUnion> {
    self.inner.get_union()
}
}
