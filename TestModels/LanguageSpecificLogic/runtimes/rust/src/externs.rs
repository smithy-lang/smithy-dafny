#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

impl crate::implementation_from_dafny::r#_LanguageSpecificLogicImpl_Compile::_default {
    pub fn GetRustRuntimeVersion(config: &::std::rc::Rc<crate::implementation_from_dafny::r#_LanguageSpecificLogicImpl_Compile::Config>) -> ::std::rc::Rc<r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::implementation_from_dafny::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>> {
        let os = ::std::env::consts::OS;
        let arch = ::std::env::consts::ARCH;
        let runtime = ::std::format!("{} {}", os, arch);

        let runtime_str = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&runtime);
        let result = r#_Wrappers_Compile::Result::Success { value: runtime_str };
        ::std::rc::Rc::new(result)
    }
}
