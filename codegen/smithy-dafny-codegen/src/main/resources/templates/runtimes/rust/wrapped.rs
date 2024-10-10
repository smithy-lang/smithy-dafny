pub mod client;

impl crate::r#$dafnyInternalModuleName:L::wrapped::_default {
  pub fn Wrapped$sdkId:L(config: &::std::rc::Rc<
      crate::r#$dafnyTypesModuleName:L::$configName:L,
  >) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$serviceName:LClient>,
          ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
  >>{
      $rustRootModuleName:L::wrapped::client::Client::from_conf(config)
  }
}