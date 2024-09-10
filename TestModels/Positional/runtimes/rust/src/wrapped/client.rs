use tokio::runtime::Runtime;

pub struct Client {
    wrapped: crate::client::Client,

    /// A `current_thread` runtime for executing operations on the
    /// asynchronous client in a blocking manner.
    rt: Runtime,
}

impl dafny_runtime::UpcastObject<dyn crate::simple::positional::internaldafny::types::ISimplePositionalClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::positional::internaldafny::types::ISimplePositionalClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
    pub fn from_conf(config: &::std::rc::Rc<
    dyn crate::simple::positional::internaldafny::types::ISimplePositionalClient,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::simple::positional::internaldafny::types::ISimplePositionalClient>,
  ::std::rc::Rc<crate::simple::positional::internaldafny::types::Error>
    >>{
        let rt_result = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build();
        let rt = match rt_result {
            Ok(x) => x,
            Err(error) => return crate::conversions::error::to_opaque_error_result(error),
        };
        let result = crate::client::Client::from_conf(
            crate::conversions::simple_positional_config::_simple_positional_config::from_dafny(
                config.clone(),
            ),
        );
        match result {
            Ok(client) => {
                let wrap = crate::wrapped::client::Client {
                    wrapped: client,
                    rt,
                };
                std::rc::Rc::new(
                    crate::_Wrappers_Compile::Result::Success {
                        value: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(wrap)),
                    },
                )
            }
            Err(error) => crate::conversions::error::to_opaque_error_result(error),
        }
    }
}

impl crate::simple::positional::internaldafny::types::ISimplePositionalClient
    for Client
{
    fn GetResource(
        &mut self,
        input: &std::rc::Rc<
            crate::simple::positional::internaldafny::types::GetResourceInput,
        >,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            std::rc::Rc<
                crate::simple::positional::internaldafny::types::GetResourceInput,
            >,
            std::rc::Rc<crate::simple::positional::internaldafny::types::Error>,
        >,
    >{
        let inner_input =
            crate::conversions::get_resource::_get_resource_input::from_dafny(input.clone());
        let result = self.rt.block_on(crate::operation::get_resource::GetResource::send(&self.wrapped, inner_input));
        match result {
            Err(error) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: crate::conversions::get_resource::to_dafny_error(error),
                },
            ),
            Ok(client) => ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Success {
                    value: crate::conversions::get_resource::_get_resource_output::to_dafny(client),
                },
            ),
        }
    }

    fn GetResourcePositional(
        &mut self,
        input: &dafny_runtime::Sequence<dafny_runtime::DafnyCharUTF16>,
    ) -> std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            dafny_runtime::Object<
                dyn crate::r#simple::positional::internaldafny::types::ISimpleResource,
            >,
            std::rc::Rc<crate::r#simple::positional::internaldafny::types::Error>,
        >,
    > {
        todo!()
    }
}
