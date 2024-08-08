use crate::tests_from_dafny::*;

impl r#simple::types::boolean::internaldafny_dwrapped::_default {
  pub fn WrappedSimpleBoolean(config: &::std::rc::Rc<
      simple_boolean_dafny::r#simple::types::boolean::internaldafny::types::SimpleBooleanConfig,
  >) -> ::std::rc::Rc<simple_boolean_dafny::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn simple_boolean_dafny::r#simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>,
          ::std::rc::Rc<simple_boolean_dafny::r#simple::types::boolean::internaldafny::types::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
