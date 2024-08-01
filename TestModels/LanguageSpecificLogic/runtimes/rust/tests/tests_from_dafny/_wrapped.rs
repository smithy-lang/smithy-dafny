use crate::tests_from_dafny::*;

impl r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default {
  pub fn WrappedLanguageSpecificLogic(config: &::std::rc::Rc<
      crate::implementation_from_dafny::r#_language_dspecific_dlogic_dinternaldafny_dtypes::LanguageSpecificLogicConfig,
  >) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>,
          ::std::rc::Rc<crate::implementation_from_dafny::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
