use tokio::runtime::Runtime;

pub struct Client {
    wrapped: crate::client::Client,

    /// A `current_thread` runtime for executing operations on the
    /// asynchronous client in a blocking manner.
    rt: Runtime
}

impl dafny_runtime::UpcastObject<dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient);
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl Client {
  pub fn from_conf(config: &::std::rc::Rc<
    crate::r#$dafnyTypesModuleName:L::$configName:L,
  >) ->
::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient>,
  ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
>> {
    let rt_result = tokio::runtime::Builder::new_current_thread()
          .enable_all()
          .build();
    let rt = match rt_result {
        Ok(x) => x,
        Err(error) => return crate::conversions::error::to_opaque_error_result(error),
    };
    let result = crate::client::Client::from_conf(
      crate::conversions::$snakeCaseConfigName:L::_$snakeCaseConfigName:L::from_dafny(
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

impl crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient for Client {
$operationImpls:L
}
