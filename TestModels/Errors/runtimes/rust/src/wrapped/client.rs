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

impl dafny_runtime::UpcastObject<dyn crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient>,
  ::std::rc::Rc<crate::r#simple::errors::internaldafny::types::Error>
>> {
    let result = crate::client::Client::from_conf(
      crate::conversions::simple_errors_config::_simple_errors_config::from_dafny(
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

impl crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient for Client {
    fn AlwaysError(
        &mut self,
        input: &::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsInput>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsOutput>,
            std::rc::Rc<crate::r#simple::errors::internaldafny::types::Error>,
        >,
    >{
        let inner_input = crate::conversions::always_error::_always_error_input::from_dafny(input.clone());
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(crate::operation::always_error::AlwaysError::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::always_error::_always_error_output::to_dafny(inner_result),
                },
            ),
        }
    }

    fn AlwaysMultipleErrors(
        &mut self,
        input: &::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsInput>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsOutput>,
            std::rc::Rc<crate::r#simple::errors::internaldafny::types::Error>,
        >,
    >{
        let inner_input = crate::conversions::always_multiple_errors::_always_multiple_errors_input::from_dafny(input.clone());
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(crate::operation::always_multiple_errors::AlwaysMultipleErrors::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::always_multiple_errors::_always_multiple_errors_output::to_dafny(inner_result),
                },
            ),
        }
    }

    fn AlwaysNativeError(
        &mut self,
        input: &::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsInput>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<crate::r#simple::errors::internaldafny::types::GetErrorsOutput>,
            std::rc::Rc<crate::r#simple::errors::internaldafny::types::Error>,
        >,
    >{
        let inner_input = crate::conversions::always_native_error::_always_native_error_input::from_dafny(input.clone());
        let result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(crate::operation::always_native_error::AlwaysNativeError::send(&self.wrapped, inner_input))
        });
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::error::to_dafny(error),
                },
            ),
            Ok(inner_result) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::always_native_error::_always_native_error_output::to_dafny(inner_result),
                },
            ),
        }
    }
}
