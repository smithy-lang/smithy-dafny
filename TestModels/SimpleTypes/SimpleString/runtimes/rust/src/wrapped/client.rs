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

impl dafny_runtime::UpcastObject<dyn crate::r#simple::types::smithystring::internaldafny::types::ISimpleTypesStringClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::types::smithystring::internaldafny::types::ISimpleTypesStringClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::types::smithystring::internaldafny::types::SimpleStringConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::types::smithystring::internaldafny::types::ISimpleTypesStringClient>,
  ::std::rc::Rc<crate::r#simple::types::smithystring::internaldafny::types::Error>
>> {
    let rt_result = tokio::runtime::Builder::new_current_thread()
          .enable_all()
          .build();
    let rt = match rt_result {
        Ok(x) => x,
        Err(error) => return crate::conversions::error::to_opaque_error_result(error),
    };
    let result = crate::client::Client::from_conf(
      crate::conversions::simple_string_config::_simple_string_config::from_dafny(
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

impl crate::r#simple::types::smithystring::internaldafny::types::ISimpleTypesStringClient for Client {
    fn GetString(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::types::smithystring::internaldafny::types::GetStringInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::types::smithystring::internaldafny::types::GetStringOutput,
            >,
            std::rc::Rc<crate::r#simple::types::smithystring::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_string::_get_string_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_string::GetString::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_string::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_string::_get_string_output::to_dafny(client),
                },
            ),
        }
    }

    fn GetStringKnownValue(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::types::smithystring::internaldafny::types::GetStringInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::types::smithystring::internaldafny::types::GetStringOutput,
            >,
            std::rc::Rc<crate::r#simple::types::smithystring::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_string_known_value::_get_string_known_value_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_string_known_value::GetStringKnownValue::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_string_known_value::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_string_known_value::_get_string_known_value_output::to_dafny(client),
                },
            ),
        }
    }

    fn GetStringUTF8(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Input,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Output,
            >,
            std::rc::Rc<crate::r#simple::types::smithystring::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_string_utf8::_get_string_utf8_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_string_utf8::GetStringUTF8::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_string_utf8::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_string_utf8::_get_string_utf8_output::to_dafny(client),
                },
            ),
        }
    }

    fn GetStringUTF8KnownValue(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Input,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Output,
            >,
            std::rc::Rc<crate::r#simple::types::smithystring::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_string_utf8_known_value::_get_string_utf8_known_value_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_string_utf8_known_value::GetStringUTF8KnownValue::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_string_utf8_known_value::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_string_utf8_known_value::_get_string_utf8_known_value_output::to_dafny(client),
                },
            ),
        }
    }
}
