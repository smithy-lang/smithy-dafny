// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`SomePrimaryOperation`](crate::operation::some_primary_operation::builders::SomePrimaryOperationFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:

    /// - On success, responds with [`SomePrimaryOperationOutput`](crate::operation::some_primary_operation::SomePrimaryOperationOutput) with field(s):

    /// - On failure, responds with [`SdkError<SomePrimaryOperationError>`](crate::operation::some_primary_operation::SomePrimaryOperationError)
    pub fn some_primary_operation(&self) -> crate::operation::some_primary_operation::builders::SomePrimaryOperationFluentBuilder {
        crate::operation::some_primary_operation::builders::SomePrimaryOperationFluentBuilder::new(self.clone())
    }
}
