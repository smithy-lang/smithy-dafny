use tokio::runtime::Runtime;

pub struct Client {
    wrapped: crate::client::Client,

    /// A `current_thread` runtime for executing operations on the
    /// asynchronous client in a blocking manner.
    rt: Runtime
}

impl dafny_runtime::UpcastObject<dyn crate::r#language::specific::logic::internaldafny::types::ILanguageSpecificLogicClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#language::specific::logic::internaldafny::types::ILanguageSpecificLogicClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#language::specific::logic::internaldafny::types::LanguageSpecificLogicConfig,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#language::specific::logic::internaldafny::types::ILanguageSpecificLogicClient>,
  ::std::rc::Rc<crate::r#language::specific::logic::internaldafny::types::Error>
>> {
    let rt_result = tokio::runtime::Builder::new_current_thread()
          .enable_all()
          .build();
    let rt = match rt_result {
        Ok(x) => x,
        Err(error) => return crate::conversions::error::to_opaque_error_result(error),
    };
    let result = crate::client::Client::from_conf(
      crate::conversions::language_specific_logic_config::_language_specific_logic_config::from_dafny(
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

impl crate::r#language::specific::logic::internaldafny::types::ILanguageSpecificLogicClient
    for Client
{
    fn GetRuntimeInformation(
        &mut self,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::r#language::specific::logic::internaldafny::types::GetRuntimeInformationOutput,
            >,
            std::rc::Rc<crate::r#language::specific::logic::internaldafny::types::Error>,
        >,
    >{
        let result = self.rt.block_on(crate::operation::get_runtime_information::GetRuntimeInformation::send(&self.wrapped));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_runtime_information::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_runtime_information::_get_runtime_information_output::to_dafny(client),
                },
            ),
        }
    }
}
