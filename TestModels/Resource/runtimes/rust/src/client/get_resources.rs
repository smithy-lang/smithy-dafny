// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`GetResources`](crate::operation::get_resources::builders::GetResourcesFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`value(impl Into<Option<::std::string::String>>)`](crate::operation::get_resources::builders::GetResourcesFluentBuilder::value) / [`set_value(Option<::std::string::String>)`](crate::operation::get_resources::builders::GetResourcesFluentBuilder::set_value): (undocumented)<br>
    /// - On success, responds with [`GetResourcesOutput`](crate::operation::get_resources::GetResourcesOutput) with field(s):
    ///   - [`output(Option<crate::types::simple_resource::SimpleResourceRef>)`](crate::operation::get_resources::GetResourcesOutput::output): (undocumented)
    /// - On failure, responds with [`SdkError<GetResourcesError>`](crate::operation::get_resources::GetResourcesError)
    pub fn get_resources(&self) -> crate::operation::get_resources::builders::GetResourcesFluentBuilder {
        crate::operation::get_resources::builders::GetResourcesFluentBuilder::new(self.clone())
    }
}
