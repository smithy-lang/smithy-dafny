// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetUnion`](crate::operation::get_union::builders::GetUnionFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`union(impl Into<Option<crate::types::MyUnion>>)`](crate::operation::get_union::builders::GetUnionFluentBuilder::union) / [`set_union(Option<crate::types::MyUnion>)`](crate::operation::get_union::builders::GetUnionFluentBuilder::set_union): (undocumented)<br>
    /// - On success, responds with [`GetUnionOutput`](crate::operation::get_union::GetUnionOutput) with field(s):
    ///   - [`union(Option<crate::types::MyUnion>)`](crate::operation::get_union::GetUnionOutput::union): (undocumented)
    /// - On failure, responds with [`SdkError<GetUnionError>`](crate::operation::get_union::GetUnionError)
    pub fn get_union(&self) -> crate::operation::get_union::builders::GetUnionFluentBuilder {
        crate::operation::get_union::builders::GetUnionFluentBuilder::new(self.clone())
    }
}
