// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use aws_smithy_types::error::operation::BuildError;

#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub struct Client {
    pub(crate) dafny_client: ::dafny_runtime::Object<dyn crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient>
}

impl Client {
    /// Creates a new client from the service [`Config`](crate::Config).
    #[track_caller]
    pub fn from_conf(
        conf: crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig,
    ) -> Result<Self, crate::deps::simple_multiplemodels_dependencyproject::types::error::Error> {
        let inner =
            crate::simple::multiplemodels::dependencyproject::internaldafny::_default::DependencyProject(
                &crate::deps::simple_multiplemodels_dependencyproject::conversions::dependency_project_config::_dependency_project_config::to_dafny(conf),
            );
        if matches!(
            inner.as_ref(),
            crate::_Wrappers_Compile::Result::Failure { .. }
        ) {
            return Err(crate::deps::simple_multiplemodels_dependencyproject::conversions::error::from_dafny(inner.as_ref().error().clone()));
        }
        Ok(Self {
            dafny_client: ::dafny_runtime::upcast_object()(inner.Extract())
        })
    }
}

mod some_dependency_operation;
