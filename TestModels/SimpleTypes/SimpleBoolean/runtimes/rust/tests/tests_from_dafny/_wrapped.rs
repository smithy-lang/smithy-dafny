use crate::tests_from_dafny::*;

impl r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default {
  pub fn WrappedSimpleBoolean(config: &::std::rc::Rc<
      crate::implementation_from_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig,
  >) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
          ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
