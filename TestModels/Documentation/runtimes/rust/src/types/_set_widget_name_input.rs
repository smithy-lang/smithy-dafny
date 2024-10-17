// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
#[allow(missing_docs)]
pub struct SetWidgetNameInput {
    #[allow(missing_docs)]
pub name: ::std::option::Option<::std::string::String>,
}
impl SetWidgetNameInput {
    #[allow(missing_docs)]
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl SetWidgetNameInput {
    /// Creates a new builder-style object to manufacture [`SetWidgetNameInput`](crate::types::SetWidgetNameInput).
    pub fn builder() -> crate::types::builders::SetWidgetNameInputBuilder {
        crate::types::builders::SetWidgetNameInputBuilder::default()
    }
}

/// A builder for [`SetWidgetNameInput`](crate::types::SetWidgetNameInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SetWidgetNameInputBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl SetWidgetNameInputBuilder {
    #[allow(missing_docs)]
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.name = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)]
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.name = input;
    self
}
#[allow(missing_docs)]
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
    /// Consumes the builder and constructs a [`SetWidgetNameInput`](crate::types::SetWidgetNameInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::SetWidgetNameInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::SetWidgetNameInput {
            name: self.name,
        })
    }
}
