// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_union::_get_union_output::GetUnionOutputBuilder;

pub use crate::operation::get_union::_get_union_input::GetUnionInputBuilder;

impl GetUnionInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_union::GetUnionOutput,
        crate::operation::get_union::GetUnionError,
    > {
        let mut fluent_builder = client.get_union();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetUnion`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetUnionFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_union::builders::GetUnionInputBuilder,
}
impl GetUnionFluentBuilder {
    /// Creates a new `GetUnion`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetUnion as a reference.
    pub fn as_input(&self) -> &crate::operation::get_union::builders::GetUnionInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_union::GetUnionOutput,
        crate::operation::get_union::GetUnionError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetUnion doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_union::GetUnionError::unhandled)?;
        crate::operation::get_union::GetUnion::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn union(mut self, input: impl ::std::convert::Into<crate::types::MyUnion>) -> Self {
    self.inner = self.inner.union(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_union(mut self, input: ::std::option::Option<crate::types::MyUnion>) -> Self {
    self.inner = self.inner.set_union(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_union(&self) -> &::std::option::Option<crate::types::MyUnion> {
    self.inner.get_union()
}
}
