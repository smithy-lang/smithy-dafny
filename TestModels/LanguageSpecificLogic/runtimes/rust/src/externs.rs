#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

impl crate::r#_LanguageSpecificLogicImpl_Compile::_default {
    pub fn GetRustRuntimeVersion(
        config: &::std::rc::Rc<crate::r#_LanguageSpecificLogicImpl_Compile::Config>,
    ) -> ::std::rc::Rc<
        crate::r#_Wrappers_Compile::Result<
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            ::std::rc::Rc<crate::r#language::specific::logic::internaldafny::types::Error>,
        >,
    > {
        let os = ::std::env::consts::OS;
        let arch = ::std::env::consts::ARCH;
        let runtime = ::std::format!("{} {}", os, arch);

        let runtime_str =
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(
                &runtime,
            );
        let result = crate::r#_Wrappers_Compile::Result::Success { value: runtime_str };
        ::std::rc::Rc::new(result)
    }
}
