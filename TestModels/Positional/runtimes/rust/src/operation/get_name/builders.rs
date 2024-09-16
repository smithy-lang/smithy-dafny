// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_name::_get_name_output::GetNameOutputBuilder;

pub use crate::operation::get_name::_get_name_input::GetNameInputBuilder;

impl GetNameInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        simple_resource: &crate::types::simple_resource::SimpleResourceRef,
    ) -> ::std::result::Result<
        crate::operation::get_name::GetNameOutput,
        crate::types::error::Error,
    > {
        let mut fluent_builder = simple_resource.get_name();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetName`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetNameFluentBuilder {
    simple_resource: crate::types::simple_resource::SimpleResourceRef,
    pub(crate) inner: crate::operation::get_name::builders::GetNameInputBuilder,
}
impl GetNameFluentBuilder {
    /// Creates a new `GetName`.
    pub(crate) fn new(simple_resource: crate::types::simple_resource::SimpleResourceRef) -> Self {
        Self {
            simple_resource,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetName as a reference.
    pub fn as_input(&self) -> &crate::operation::get_name::builders::GetNameInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_name::GetNameOutput,
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
        crate::operation::get_name::GetName::send(&self.simple_resource, input).await
    }


}
