// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::get_enum_v2_third_known_value_test::_get_enum_v2_output::GetEnumV2OutputBuilder;

pub use crate::operation::get_enum_v2_third_known_value_test::_get_enum_v2_input::GetEnumV2InputBuilder;

impl GetEnumV2InputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::get_enum_v2_third_known_value_test::GetEnumV2Output,
        crate::operation::get_enum_v2_third_known_value_test::GetEnumV2ThirdKnownValueTestError,
    > {
        let mut fluent_builder = client.get_enum_v2_third_known_value_test();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `GetEnumV2ThirdKnownValueTest`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct GetEnumV2ThirdKnownValueTestFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::get_enum_v2_third_known_value_test::builders::GetEnumV2InputBuilder,
}
impl GetEnumV2ThirdKnownValueTestFluentBuilder {
    /// Creates a new `GetEnumV2ThirdKnownValueTest`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the GetEnumV2ThirdKnownValueTest as a reference.
    pub fn as_input(&self) -> &crate::operation::get_enum_v2_third_known_value_test::builders::GetEnumV2InputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_enum_v2_third_known_value_test::GetEnumV2Output,
        crate::operation::get_enum_v2_third_known_value_test::GetEnumV2ThirdKnownValueTestError,
    > {
        let input = self
            .inner
            .build()
            // Using unhandled since GetEnumV2ThirdKnownValueTest doesn't declare any validation,
            // and smithy-rs seems to not generate a ValidationError case unless there is
            // (but isn't that a backwards compatibility problem for output structures?)
            // Vanilla smithy-rs uses SdkError::construction_failure,
            // but we aren't using SdkError.
            .map_err(crate::operation::get_enum_v2_third_known_value_test::GetEnumV2ThirdKnownValueTestError::unhandled)?;
        crate::operation::get_enum_v2_third_known_value_test::GetEnumV2ThirdKnownValueTest::send(&self.client, input).await
    }

    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<crate::types::SimpleEnumV2Shape>) -> Self {
    self.inner = self.inner.value(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<crate::types::SimpleEnumV2Shape>) -> Self {
    self.inner = self.inner.set_value(input);
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<crate::types::SimpleEnumV2Shape> {
    self.inner.get_value()
}
}
