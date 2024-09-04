// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_aggregate::_get_aggregate_output::GetAggregateOutputBuilder;

pub use crate::operation::get_aggregate::_get_aggregate_input::GetAggregateInputBuilder;

impl GetAggregateInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_aggregate::GetAggregateOutput,
        crate::operation::get_aggregate::GetAggregateError,
    > {
        let mut fluent_builder = client.get_aggregate();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetAggregate`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetAggregateFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_aggregate::builders::GetAggregateInputBuilder,
}
impl GetAggregateFluentBuilder {
    /// Creates a new `GetAggregate`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetAggregate as a reference.
    pub fn as_input(&self) -> &crate::operation::get_aggregate::builders::GetAggregateInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_aggregate::GetAggregateOutput,
        crate::operation::get_aggregate::GetAggregateError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetAggregate doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_aggregate::GetAggregateError::unhandled)?;
        crate::operation::get_aggregate::GetAggregate::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn nested_structure(mut self, input: impl ::std::convert::Into<crate::types::NestedStructure>) -> Self {
    self.inner = self.inner.nested_structure(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_nested_structure(mut self, input: ::std::option::Option<crate::types::NestedStructure>) -> Self {
    self.inner = self.inner.set_nested_structure(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_nested_structure(&self) -> &::std::option::Option<crate::types::NestedStructure> {
    self.inner.get_nested_structure()
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_integer_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>) -> Self {
    self.inner = self.inner.simple_integer_map(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_integer_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>>) -> Self {
    self.inner = self.inner.set_simple_integer_map(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_integer_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::primitive::i32>> {
    self.inner.get_simple_integer_map()
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.simple_string_list(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_string_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_simple_string_list(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_string_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_simple_string_list()
}
#[allow(missing_docs)] // documentation missing in model
pub fn simple_string_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.simple_string_map(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_simple_string_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.set_simple_string_map(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_simple_string_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    self.inner.get_simple_string_map()
}
#[allow(missing_docs)] // documentation missing in model
pub fn structure_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<crate::types::StructureListElement>>) -> Self {
    self.inner = self.inner.structure_list(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_structure_list(mut self, input: ::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>>) -> Self {
    self.inner = self.inner.set_structure_list(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_structure_list(&self) -> &::std::option::Option<::std::vec::Vec<crate::types::StructureListElement>> {
    self.inner.get_structure_list()
}
}
