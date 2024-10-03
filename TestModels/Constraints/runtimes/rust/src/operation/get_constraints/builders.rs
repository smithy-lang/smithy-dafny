// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_constraints::_get_constraints_output::GetConstraintsOutputBuilder;

pub use crate::operation::get_constraints::_get_constraints_input::GetConstraintsInputBuilder;

impl GetConstraintsInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::client::Client,
    ) -> ::std::result::Result<
        crate::operation::get_constraints::GetConstraintsOutput,
        crate::types::error::Error,
    > {
        let mut fluent_builder = client.get_constraints();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetConstraints`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetConstraintsFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_constraints::builders::GetConstraintsInputBuilder,
}
impl GetConstraintsFluentBuilder {
    /// Creates a new `GetConstraints`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetConstraints as a reference.
    pub fn as_input(&self) -> &crate::operation::get_constraints::builders::GetConstraintsInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_constraints::GetConstraintsOutput,
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
        crate::operation::get_constraints::GetConstraints::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn blob_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.blob_less_than_or_equal_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_blob_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_blob_less_than_or_equal_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_blob_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_blob_less_than_or_equal_to_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn greater_than_one(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.inner = self.inner.greater_than_one(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_greater_than_one(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.inner = self.inner.set_greater_than_one(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_greater_than_one(&self) -> &::std::option::Option<::std::primitive::i32> {
    self.inner.get_greater_than_one()
}
#[allow(missing_docs)] // documentation missing in model
pub fn less_than_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.inner = self.inner.less_than_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_less_than_ten(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.inner = self.inner.set_less_than_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_less_than_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    self.inner.get_less_than_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn list_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.list_less_than_or_equal_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_list_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_list_less_than_or_equal_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_list_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_list_less_than_or_equal_to_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn map_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.map_less_than_or_equal_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_map_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.set_map_less_than_or_equal_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_map_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    self.inner.get_map_less_than_or_equal_to_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_blob(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.my_blob(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_blob(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_my_blob(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_my_blob()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.my_list(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_my_list(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_my_list()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_list_of_utf8_bytes(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.my_list_of_utf8_bytes(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_list_of_utf8_bytes(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_my_list_of_utf8_bytes(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_list_of_utf8_bytes(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_my_list_of_utf8_bytes()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.my_map(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.set_my_map(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    self.inner.get_my_map()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_string(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.my_string(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_string(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_my_string(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_string(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_my_string()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_utf8_bytes(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.my_utf8_bytes(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_utf8_bytes(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_my_utf8_bytes(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_utf8_bytes(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_my_utf8_bytes()
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_blob(mut self, input: impl ::std::convert::Into<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.non_empty_blob(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_blob(mut self, input: ::std::option::Option<::aws_smithy_types::Blob>) -> Self {
    self.inner = self.inner.set_non_empty_blob(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_blob(&self) -> &::std::option::Option<::aws_smithy_types::Blob> {
    self.inner.get_non_empty_blob()
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_list(mut self, input: impl ::std::convert::Into<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.non_empty_list(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_list(mut self, input: ::std::option::Option<::std::vec::Vec<::std::string::String>>) -> Self {
    self.inner = self.inner.set_non_empty_list(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_list(&self) -> &::std::option::Option<::std::vec::Vec<::std::string::String>> {
    self.inner.get_non_empty_list()
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_map(mut self, input: impl ::std::convert::Into<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.non_empty_map(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_map(mut self, input: ::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>>) -> Self {
    self.inner = self.inner.set_non_empty_map(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_map(&self) -> &::std::option::Option<::std::collections::HashMap<::std::string::String, ::std::string::String>> {
    self.inner.get_non_empty_map()
}
#[allow(missing_docs)] // documentation missing in model
pub fn non_empty_string(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.non_empty_string(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_non_empty_string(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_non_empty_string(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_non_empty_string(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_non_empty_string()
}
#[allow(missing_docs)] // documentation missing in model
pub fn one_to_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.inner = self.inner.one_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_one_to_ten(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.inner = self.inner.set_one_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_one_to_ten(&self) -> &::std::option::Option<::std::primitive::i32> {
    self.inner.get_one_to_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn string_less_than_or_equal_to_ten(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.string_less_than_or_equal_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_string_less_than_or_equal_to_ten(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_string_less_than_or_equal_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_string_less_than_or_equal_to_ten(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_string_less_than_or_equal_to_ten()
}
#[allow(missing_docs)] // documentation missing in model
pub fn my_ten_to_ten(mut self, input: impl ::std::convert::Into<::std::primitive::i64>) -> Self {
    self.inner = self.inner.my_ten_to_ten(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_my_ten_to_ten(mut self, input: ::std::option::Option<::std::primitive::i64>) -> Self {
    self.inner = self.inner.set_my_ten_to_ten(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_my_ten_to_ten(&self) -> &::std::option::Option<::std::primitive::i64> {
    self.inner.get_my_ten_to_ten()
}
}
