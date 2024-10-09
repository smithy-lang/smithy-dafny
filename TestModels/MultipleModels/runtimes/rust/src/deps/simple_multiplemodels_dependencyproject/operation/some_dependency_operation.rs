// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Orchestration and serialization glue logic for `SomeDependencyOperation`.
#[derive(::std::clone::Clone, ::std::default::Default, ::std::fmt::Debug)]
#[non_exhaustive]
pub struct SomeDependencyOperation;
impl SomeDependencyOperation {
    /// Creates a new `SomeDependencyOperation`
    pub fn new() -> Self {
        Self
    }

    pub(crate) async fn send(
        client: &crate::deps::simple_multiplemodels_dependencyproject::client::Client,
        input: crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperationInput,
    ) -> ::std::result::Result<
        crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperationOutput,
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error,
    > {

                let inner_input = crate::deps::simple_multiplemodels_dependencyproject::conversions::some_dependency_operation::_some_dependency_operation_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(client.dafny_client.clone()).SomeDependencyOperation(&inner_input);
        if matches!(
            inner_result.as_ref(),
            crate::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::deps::simple_multiplemodels_dependencyproject::conversions::some_dependency_operation::_some_dependency_operation_output::from_dafny(inner_result.value().clone()),
            )
        } else {
            Err(crate::deps::simple_multiplemodels_dependencyproject::conversions::error::from_dafny(
                inner_result.error().clone(),
            ))
        }
    }
}

pub use crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::_some_dependency_operation_output::SomeDependencyOperationOutput;

pub use crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::_some_dependency_operation_input::SomeDependencyOperationInput;

pub(crate) mod _some_dependency_operation_output;

pub(crate) mod _some_dependency_operation_input;

/// Builders
pub mod builders;
