// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
impl crate::client::Client {
    /// Constructs a fluent builder for the [`SomeDependencyOperation`](crate::operation::some_dependency_operation::builders::SomeDependencyOperationFluentBuilder) operation.
    ///
    /// - The fluent builder is configurable:

    /// - On success, responds with [`SomeDependencyOperationOutput`](crate::operation::some_dependency_operation::SomeDependencyOperationOutput) with field(s):

    /// - On failure, responds with [`SdkError<SomeDependencyOperationError>`](crate::operation::some_dependency_operation::SomeDependencyOperationError)
    pub fn some_dependency_operation(&self) -> crate::operation::some_dependency_operation::builders::SomeDependencyOperationFluentBuilder {
        crate::operation::some_dependency_operation::builders::SomeDependencyOperationFluentBuilder::new(self.clone())
    }
}
