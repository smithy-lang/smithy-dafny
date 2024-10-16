// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use std::sync::LazyLock;

pub struct Client {
    wrapped: crate::client::Client
}

/// A runtime for executing operations on the asynchronous client in a blocking manner.
/// Necessary because Dafny only generates synchronous code.
static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
          .enable_all()
          .build()
          .unwrap()
});

impl dafny_runtime::UpcastObject<dyn crate::r#simple::constraints::internaldafny::types::ISimpleConstraintsClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::constraints::internaldafny::types::ISimpleConstraintsClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::constraints::internaldafny::types::ISimpleConstraintsClient>,
  ::std::rc::Rc<crate::r#simple::constraints::internaldafny::types::Error>
>> {
    let result = crate::client::Client::from_conf(
      crate::conversions::simple_constraints_config::_simple_constraints_config::from_dafny(
          config.clone(),
      ),
    );
    match result {
      Ok(client) =>  {
        let wrap = crate::wrapped::client::Client {
          wrapped: client
        };
        std::rc::Rc::new(
          crate::_Wrappers_Compile::Result::Success {
            value: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(wrap))
          }
        )
      },
      Err(error) => crate::conversions::error::to_opaque_error_result(error)
    }
  }
}

impl crate::r#simple::constraints::internaldafny::types::ISimpleConstraintsClient for Client {
    fn GetConstraints(
        &mut self,
        input: &::std::rc::Rc<crate::r#simple::constraints::internaldafny::types::GetConstraintsInput>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<crate::r#simple::constraints::internaldafny::types::GetConstraintsOutput>,
            std::rc::Rc<crate::r#simple::constraints::internaldafny::types::Error>,
        >,
    >{
        let inner_input = crate::conversions::get_constraints::_get_constraints_input::from_dafny(input.clone());
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(crate::operation::get_constraints::GetConstraints::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_constraints::_get_constraints_output::to_dafny(inner_result),
                },
            ),
        }
    }
}
