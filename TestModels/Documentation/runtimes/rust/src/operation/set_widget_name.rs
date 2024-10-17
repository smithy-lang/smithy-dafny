// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `SetWidgetName`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct SetWidgetName;
impl SetWidgetName {
    /// Creates a new `SetWidgetName`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        widget: &crate::types::widget::WidgetRef,
        input: crate::operation::set_widget_name::SetWidgetNameInput,
    ) -> ::std::result::Result<
        (),
        crate::types::error::Error,
    > {
        if input.name.is_none() {
    return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
        "name",
        "name was not specified but it is required when building SetWidgetNameInput",
    )).map_err(crate::types::error::Error::wrap_validation_err);
}
        widget.inner.borrow_mut().set_widget_name(input)
    }
}

pub use crate::operation::set_widget_name::_unit::Unit;

pub use crate::operation::set_widget_name::_set_widget_name_input::SetWidgetNameInput;

pub(crate) mod _unit;

pub(crate) mod _set_widget_name_input;

/// Builders
pub mod builders;
