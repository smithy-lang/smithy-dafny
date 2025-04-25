use std::sync::LazyLock;

pub struct Client {
    wrapped: $rustRootModuleName:L::client::Client
}

/// A runtime for executing operations on the asynchronous client in a blocking manner.
/// Necessary because Dafny only generates synchronous code.
static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
          .enable_all()
          .build()
          .unwrap()
});

impl dafny_runtime::UpcastObject<dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient);
}

impl dafny_runtime::UpcastObject<::dafny_runtime::DynAny> for Client {
    ::dafny_runtime::UpcastObjectFn!(::dafny_runtime::DynAny);
}

impl Client {
  pub fn from_conf(config: &::dafny_runtime::Rc<
    crate::r#$dafnyTypesModuleName:L::$configName:L,
  >) ->
::dafny_runtime::Rc<crate::r#_Wrappers_Compile::Result<
  ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient>,
  ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>
>> {
    let result = $rustRootModuleName:L::client::Client::from_conf(
      $rustRootModuleName:L::conversions::$snakeCaseConfigName:L::_$snakeCaseConfigName:L::from_dafny(
          config.clone(),
      ),
    );
    match result {
      Ok(client) =>  {
        let wrap = $rustRootModuleName:L::wrapped::client::Client {
          wrapped: client
        };
        dafny_runtime::Rc::new(
          crate::_Wrappers_Compile::Result::Success {
            value: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(wrap))
          }
        )
      },
	Err(error) => {
          let msg = format!("{:?}", error);
	  $rustRootModuleName:L::conversions::error::to_opaque_error_result(msg)
	}
    }
  }
}

impl crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient for Client {
$operationImpls:L
}
