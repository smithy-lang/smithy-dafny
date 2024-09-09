// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_resource_data::_get_resource_data_output::GetResourceDataOutputBuilder;

pub use crate::operation::get_resource_data::_get_resource_data_input::GetResourceDataInputBuilder;

impl GetResourceDataInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        simple_resource: &crate::types::simple_resource::SimpleResourceRef,
    ) -> ::std::result::Result<
        crate::operation::get_resource_data::GetResourceDataOutput,
        crate::operation::get_resource_data::GetResourceDataError,
    > {
        let mut fluent_builder = simple_resource.get_resource_data();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetResourceData`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetResourceDataFluentBuilder {
    simple_resource: crate::types::simple_resource::SimpleResourceRef,
    pub(crate) inner: crate::operation::get_resource_data::builders::GetResourceDataInputBuilder,
}
impl GetResourceDataFluentBuilder {
    /// Creates a new `GetResourceData`.
    pub(crate) fn new(simple_resource: crate::types::simple_resource::SimpleResourceRef) -> Self {
        Self {
            simple_resource,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetResourceData as a reference.
    pub fn as_input(&self) -> &crate::operation::get_resource_data::builders::GetResourceDataInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resource_data::GetResourceDataOutput,
        crate::operation::get_resource_data::GetResourceDataError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetResourceData doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_resource_data::GetResourceDataError::unhandled)?;
        crate::operation::get_resource_data::GetResourceData::send(&self.simple_resource, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn blob_value(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.blob_value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_blob_value(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_blob_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_blob_value(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_blob_value()
}
#[allow(missing_docs)] // documentation missing in model
pub fn boolean_value(mut self, input: impl ::std::convert::Into<::std::primitive::bool>) -> Self {
    self.inner = self.inner.boolean_value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_boolean_value(mut self, input: ::std::option::Option<::std::primitive::bool>) -> Self {
    self.inner = self.inner.set_boolean_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_boolean_value(&self) -> &::std::option::Option<::std::primitive::bool> {
    self.inner.get_boolean_value()
}
#[allow(missing_docs)] // documentation missing in model
pub fn integer_value(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.inner = self.inner.integer_value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_integer_value(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.inner = self.inner.set_integer_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_integer_value(&self) -> &::std::option::Option<::std::primitive::i32> {
    self.inner.get_integer_value()
}
#[allow(missing_docs)] // documentation missing in model
pub fn long_value(mut self, input: impl ::std::convert::Into<::std::primitive::i64>) -> Self {
    self.inner = self.inner.long_value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_long_value(mut self, input: ::std::option::Option<::std::primitive::i64>) -> Self {
    self.inner = self.inner.set_long_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_long_value(&self) -> &::std::option::Option<::std::primitive::i64> {
    self.inner.get_long_value()
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_value(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.string_value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_string_value(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_string_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_string_value(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_string_value()
}
}
