// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_enum_first_known_value_test::_get_enum_output::GetEnumOutputBuilder;

pub use crate::operation::get_enum_first_known_value_test::_get_enum_input::GetEnumInputBuilder;

impl GetEnumInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_enum_first_known_value_test::GetEnumOutput,
        crate::operation::get_enum_first_known_value_test::GetEnumFirstKnownValueTestError,
    > {
        let mut fluent_builder = client.get_enum_first_known_value_test();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetEnumFirstKnownValueTest`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetEnumFirstKnownValueTestFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_enum_first_known_value_test::builders::GetEnumInputBuilder,
}
impl GetEnumFirstKnownValueTestFluentBuilder {
    /// Creates a new `GetEnumFirstKnownValueTest`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetEnumFirstKnownValueTest as a reference.
    pub fn as_input(&self) -> &crate::operation::get_enum_first_known_value_test::builders::GetEnumInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_enum_first_known_value_test::GetEnumOutput,
        crate::operation::get_enum_first_known_value_test::GetEnumFirstKnownValueTestError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetEnumFirstKnownValueTest doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_enum_first_known_value_test::GetEnumFirstKnownValueTestError::unhandled)?;
        crate::operation::get_enum_first_known_value_test::GetEnumFirstKnownValueTest::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<crate::types::SimpleEnumShape>) -> Self {
    self.inner = self.inner.value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<crate::types::SimpleEnumShape>) -> Self {
    self.inner = self.inner.set_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<crate::types::SimpleEnumShape> {
    self.inner.get_value()
}
}
