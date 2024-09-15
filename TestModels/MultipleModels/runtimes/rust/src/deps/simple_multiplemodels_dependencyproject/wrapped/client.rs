// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use std::sync::LazyLock;

pub struct Client {
    wrapped: crate::deps::simple_multiplemodels_dependencyproject::client::Client
}

/// A runtime for executing operations on the asynchronous client in a blocking manner.
/// Necessary because Dafny only generates synchronous code.
static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
          .enable_all()
          .build()
          .unwrap()
});

impl dafny_runtime::UpcastObject<dyn crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient>,
  ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error>
>> {
    let result = crate::deps::simple_multiplemodels_dependencyproject::client::Client::from_conf(
      crate::deps::simple_multiplemodels_dependencyproject::conversions::dependency_project_config::_dependency_project_config::from_dafny(
          config.clone(),
      ),
    );
    match result {
      Ok(client) =>  {
        let wrap = crate::deps::simple_multiplemodels_dependencyproject::wrapped::client::Client {
          wrapped: client
        };
        std::rc::Rc::new(
          crate::_Wrappers_Compile::Result::Success {
            value: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(wrap))
          }
        )
      },
      Err(error) => crate::deps::simple_multiplemodels_dependencyproject::conversions::error::to_opaque_error_result(error)
    }
  }
}

impl crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient for Client {
    fn SomeDependencyOperation(
        &mut self,
        input: &::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::SomeDependencyOperationInput>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::SomeDependencyOperationOutput>,
            std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error>,
        >,
    >{
        let inner_input = crate::deps::simple_multiplemodels_dependencyproject::conversions::some_dependency_operation::_some_dependency_operation_input::from_dafny(input.clone());
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(crate::deps::simple_multiplemodels_dependencyproject::operation::some_dependency_operation::SomeDependencyOperation::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::deps::simple_multiplemodels_dependencyproject::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::deps::simple_multiplemodels_dependencyproject::conversions::some_dependency_operation::_some_dependency_operation_output::to_dafny(inner_result),
                },
            ),
        }
    }
}
