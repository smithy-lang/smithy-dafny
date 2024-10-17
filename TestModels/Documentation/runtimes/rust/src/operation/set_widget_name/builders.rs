// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub use crate::operation::set_widget_name::_unit::UnitBuilder;

pub use crate::operation::set_widget_name::_set_widget_name_input::SetWidgetNameInputBuilder;

impl SetWidgetNameInputBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        widget: &crate::types::widget::WidgetRef,
    ) -> ::std::result::Result<
        (),
        crate::types::error::Error,
    > {
        let mut fluent_builder = widget.set_widget_name();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `SetWidgetName`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct SetWidgetNameFluentBuilder {
    widget: crate::types::widget::WidgetRef,
    pub(crate) inner: crate::operation::set_widget_name::builders::SetWidgetNameInputBuilder,
}
impl SetWidgetNameFluentBuilder {
    /// Creates a new `SetWidgetName`.
    pub(crate) fn new(widget: crate::types::widget::WidgetRef) -> Self {
        Self {
            widget,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the SetWidgetName as a reference.
    pub fn as_input(&self) -> &crate::operation::set_widget_name::builders::SetWidgetNameInputBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        (),
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
                obj: ::dafny_runtime::Object::from_ref(&mut e as &mut dyn ::std::any::Any),
		alt_text : format!("{:?}", e)
            })?;
        crate::operation::set_widget_name::SetWidgetName::send(&self.widget, input).await
    }

    #[allow(missing_docs)]
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.inner = self.inner.name(input.into());
    self
}
#[allow(missing_docs)]
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.inner = self.inner.set_name(input);
    self
}
#[allow(missing_docs)]
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    self.inner.get_name()
}
}
