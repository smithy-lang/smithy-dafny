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

impl dafny_runtime::UpcastObject<dyn crate::r#simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#simple::types::timestamp::internaldafny::types::SimpleTimestampConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>,
  ::std::rc::Rc<crate::r#simple::types::timestamp::internaldafny::types::Error>
>> {
    let rt_result = tokio::runtime::Builder::new_current_thread()
          .enable_all()
          .build();
    let rt = match rt_result {
        Ok(x) => x,
        Err(error) => return crate::conversions::error::to_opaque_error_result(error),
    };
    let result = crate::client::Client::from_conf(
      crate::conversions::simple_timestamp_config::_simple_timestamp_config::from_dafny(
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

impl crate::r#simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient for Client {
    fn GetTimestamp(
        &mut self,
        input: &std::rc::Rc<
            crate::r#simple::types::timestamp::internaldafny::types::GetTimestampInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#simple::types::timestamp::internaldafny::types::GetTimestampOutput,
            >,
            std::rc::Rc<crate::r#simple::types::timestamp::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_timestamp::_get_timestamp_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_timestamp::GetTimestamp::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_timestamp::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_timestamp::_get_timestamp_output::to_dafny(client),
                },
            ),
        }
    }
}
