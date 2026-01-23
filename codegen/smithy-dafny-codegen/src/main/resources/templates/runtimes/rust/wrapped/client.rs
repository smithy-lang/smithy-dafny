use std::future::Future;
use tokio::runtime::RuntimeFlavor;
use tokio::runtime::Handle;
use tokio::runtime::Builder;

pub fn escape_to_async<F, O>(fut: F) -> O
where
    F: Future<Output = O> + Send,
    O: Send
{
    match Handle::try_current() {
        Ok(handle) => {
            match handle.runtime_flavor() {
                RuntimeFlavor::CurrentThread => {
                    std::thread::scope(move |t| {
                        t.spawn(move || {
                            Builder::new_current_thread().enable_all().build().unwrap().block_on(fut)
                        }).join().unwrap()
                    })
                },
                _ => {
                    tokio::task::block_in_place(move || {
                        handle.block_on(fut)
                    })
                }
            }

        },
        Err(_) => {
            Builder::new_current_thread().enable_all().build().unwrap().block_on(fut)
        }
    }
}

pub struct Client {
    wrapped: $rustRootModuleName:L::client::Client
}

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
