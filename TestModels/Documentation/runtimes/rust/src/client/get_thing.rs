// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`GetThing`](crate::operation::get_thing::builders::GetThingFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`name(impl Into<Option<::std::string::String>>)`](crate::operation::get_thing::builders::GetThingFluentBuilder::name) / [`set_name(Option<::std::string::String>)`](crate::operation::get_thing::builders::GetThingFluentBuilder::set_name): (undocumented)<br>
    /// - On success, responds with [`GetThingOutput`](crate::operation::get_thing::GetThingOutput) with field(s):
    ///   - [`thing(Option<crate::types::Thing>)`](crate::operation::get_thing::GetThingOutput::thing): (undocumented)
    /// - On failure, responds with [`SdkError<GetThingError>`](crate::operation::get_thing::GetThingError)
    pub fn get_thing(&self) -> crate::operation::get_thing::builders::GetThingFluentBuilder {
        crate::operation::get_thing::builders::GetThingFluentBuilder::new(self.clone())
    }
}
