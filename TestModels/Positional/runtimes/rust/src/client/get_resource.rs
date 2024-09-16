// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`GetResource`](crate::operation::get_resource::builders::GetResourceFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`name(impl Into<Option<::std::string::String>>)`](crate::operation::get_resource::builders::GetResourceFluentBuilder::name) / [`set_name(Option<::std::string::String>)`](crate::operation::get_resource::builders::GetResourceFluentBuilder::set_name): (undocumented)<br>
    /// - On success, responds with [`GetResourceOutput`](crate::operation::get_resource::GetResourceOutput) with field(s):
    ///   - [`output(Option<crate::types::simple_resource::SimpleResourceRef>)`](crate::operation::get_resource::GetResourceOutput::output): (undocumented)
    /// - On failure, responds with [`SdkError<GetResourceError>`](crate::operation::get_resource::GetResourceError)
    pub fn get_resource(&self) -> crate::operation::get_resource::builders::GetResourceFluentBuilder {
        crate::operation::get_resource::builders::GetResourceFluentBuilder::new(self.clone())
    }
}
