// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use tokio::runtime::Runtime;

pub struct Client {
    wrapped: crate::client::Client,

    /// A `current_thread` runtime for executing operations on the
    /// asynchronous client in a blocking manner.
    rt: Runtime
}

impl dafny_runtime::UpcastObject<dyn crate::r#simple::union::internaldafny::types::ISimpleUnionClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::union::internaldafny::types::ISimpleUnionClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::union::internaldafny::types::SimpleUnionConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::union::internaldafny::types::ISimpleUnionClient>,
  ::std::rc::Rc<crate::r#simple::union::internaldafny::types::Error>
>> {
    let rt_result = tokio::runtime::Builder::new_current_thread()
          .enable_all()
          .build();
    let rt = match rt_result {
        Ok(x) => x,
        Err(error) => return crate::conversions::error::to_opaque_error_result(error),
    };
    let result = crate::client::Client::from_conf(
      crate::conversions::simple_union_config::_simple_union_config::from_dafny(
          config.clone(),
      ),
    );
    match result {
      Ok(client) =>  {
        let wrap = crate::wrapped::client::Client {
          wrapped: client,
          rt
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

impl crate::r#simple::union::internaldafny::types::ISimpleUnionClient for Client {
    fn GetKnownValueUnion(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::union::internaldafny::types::GetKnownValueUnionInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::union::internaldafny::types::GetKnownValueUnionOutput,
            >,
            std::rc::Rc<crate::r#simple::union::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_known_value_union::_get_known_value_union_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_known_value_union::GetKnownValueUnion::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_known_value_union::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_known_value_union::_get_known_value_union_output::to_dafny(client),
                },
            ),
        }
    }

    fn GetUnion(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::union::internaldafny::types::GetUnionInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::union::internaldafny::types::GetUnionOutput,
            >,
            std::rc::Rc<crate::r#simple::union::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_union::_get_union_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_union::GetUnion::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_union::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_union::_get_union_output::to_dafny(client),
                },
            ),
        }
    }
}
