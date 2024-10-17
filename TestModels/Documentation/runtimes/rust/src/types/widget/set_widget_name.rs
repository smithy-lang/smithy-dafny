// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::types::widget::WidgetRef {
    /// Constructs a fluent builder for the [`SetWidgetName`](crate::operation::set_widget_name::builders::SetWidgetNameFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`name(impl Into<Option<::std::string::String>>)`](crate::operation::set_widget_name::builders::SetWidgetNameFluentBuilder::name) / [`set_name(Option<::std::string::String>)`](crate::operation::set_widget_name::builders::SetWidgetNameFluentBuilder::set_name): (undocumented)<br>
    /// - On success, responds with [`Unit`](crate::operation::set_widget_name::Unit) with field(s):

    /// - On failure, responds with [`SdkError<SetWidgetNameError>`](crate::operation::set_widget_name::SetWidgetNameError)
    pub fn set_widget_name(&self) -> crate::operation::set_widget_name::builders::SetWidgetNameFluentBuilder {
        crate::operation::set_widget_name::builders::SetWidgetNameFluentBuilder::new(self.clone())
    }
}
