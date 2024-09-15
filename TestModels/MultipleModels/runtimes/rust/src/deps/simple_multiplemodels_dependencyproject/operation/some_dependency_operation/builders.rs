// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::_some_dependency_operation_output::SomeDependencyOperationOutputBuilder;

pub use crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::_some_dependency_operation_input::SomeDependencyOperationInputBuilder;

impl SomeDependencyOperationInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::deps::simple_multiplemodels_dependencyproject::client::Client,
    ) -> ::std::result::Result<
        crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperationOutput,
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error,
    > {
        let mut fluent_builder = client.some_dependency_operation();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `SomeDependencyOperation`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SomeDependencyOperationFluentBuilder {
    client: crate::deps::simple_multiplemodels_dependencyproject::client::Client,
    pub(crate) inner: crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::builders::SomeDependencyOperationInputBuilder,
}
impl SomeDependencyOperationFluentBuilder {
    /// Creates a new `SomeDependencyOperation`.
    pub(crate) fn new(client: crate::deps::simple_multiplemodels_dependencyproject::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the SomeDependencyOperation as a reference.
    pub fn as_input(&self) -> &crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::builders::SomeDependencyOperationInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperationOutput,
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error,
    > {
        let input = self
            .inner
            .build()
            // Using Opaque since we don't have a validation-specific error yet.
            // Operations' models don't declare their own validation error,
            // and smithy-rs seems to not generate a ValidationError case unless there is.
            // Vanilla smithy-rs uses SdkError::construction_failure, but we aren't using SdkError.
            .map_err(|mut e| crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::Opaque {
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any)
            })?;
        crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperation::send(&self.client, input).await
    }


}
