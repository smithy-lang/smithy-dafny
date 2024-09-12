// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`GetResourcePositional`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`name(impl Into<Option<::std::string::String>>)`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::name) / [`set_name(Option<::std::string::String>)`](crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::set_name): (undocumented)<br>
    /// - On success, responds with [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::GetResourcePositionalOutput) with field(s):
    ///   - [`output(Option<crate::types::simple_resource::SimpleResourceRef>)`](crate::operation::get_resource_positional::GetResourcePositionalOutput::output): (undocumented)
    /// - On failure, responds with [`SdkError<GetResourcePositionalError>`](crate::operation::get_resource_positional::GetResourcePositionalError)
    pub fn get_resource_positional(&self) -> crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder {
        crate::operation::get_resource_positional::builders::GetResourcePositionalFluentBuilder::new(self.clone())
    }
}
