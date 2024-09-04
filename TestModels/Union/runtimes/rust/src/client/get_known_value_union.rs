// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl super::Client {
    /// Constructs a fluent builder for the [`GetKnownValueUnion`](crate::operation::get_known_value_union::builders::GetKnownValueUnionFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:
    ///   - [`union(impl Into<Option<crate::types::KnownValueUnion>>)`](crate::operation::get_known_value_union::builders::GetKnownValueUnionFluentBuilder::union) / [`set_union(Option<crate::types::KnownValueUnion>)`](crate::operation::get_known_value_union::builders::GetKnownValueUnionFluentBuilder::set_union): (undocumented)<br>
    /// - On success, responds with [`GetKnownValueUnionOutput`](crate::operation::get_known_value_union::GetKnownValueUnionOutput) with field(s):
    ///   - [`union(Option<crate::types::KnownValueUnion>)`](crate::operation::get_known_value_union::GetKnownValueUnionOutput::union): (undocumented)
    /// - On failure, responds with [`SdkError<GetKnownValueUnionError>`](crate::operation::get_known_value_union::GetKnownValueUnionError)
    pub fn get_known_value_union(&self) -> crate::operation::get_known_value_union::builders::GetKnownValueUnionFluentBuilder {
        crate::operation::get_known_value_union::builders::GetKnownValueUnionFluentBuilder::new(self.clone())
    }
}
