// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::some_primary_operation::_some_primary_operation_output::SomePrimaryOperationOutputBuilder;

pub use crate::operation::some_primary_operation::_some_primary_operation_input::SomePrimaryOperationInputBuilder;

impl SomePrimaryOperationInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::client::Client,
    ) -> ::std::result::Result<
        crate::operation::some_primary_operation::SomePrimaryOperationOutput,
        crate::types::error::Error,
    > {
        let mut fluent_builder = client.some_primary_operation();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `SomePrimaryOperation`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SomePrimaryOperationFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::some_primary_operation::builders::SomePrimaryOperationInputBuilder,
}
impl SomePrimaryOperationFluentBuilder {
    /// Creates a new `SomePrimaryOperation`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the SomePrimaryOperation as a reference.
    pub fn as_input(&self) -> &crate::operation::some_primary_operation::builders::SomePrimaryOperationInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::some_primary_operation::SomePrimaryOperationOutput,
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
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any)
            })?;
        crate::operation::some_primary_operation::SomePrimaryOperation::send(&self.client, input).await
    }


}
