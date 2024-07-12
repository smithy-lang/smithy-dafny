use crate::tests_from_dafny::*;

impl r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default {
  pub fn WrappedSimpleBoolean(config: &::std::rc::Rc<
      ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig,
  >) -> ::std::rc::Rc<::simple_boolean_dafny::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn ::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
          ::std::rc::Rc<::simple_boolean_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
