#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

use language_specific_logic::implementation_from_dafny::*;
use language_specific_logic::*;
mod _wrapped;

pub mod r#_language_dspecific_dlogic_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultLanguageSpecificLogicConfig() -> ::std::rc::Rc<
            super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::LanguageSpecificLogicConfig,
        > {
            super::r#_language_dspecific_dlogic_dinternaldafny::_default::DefaultLanguageSpecificLogicConfig()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_LanguageSpecificLogicImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn RustSpecificTests() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny::_default::LanguageSpecificLogic(&super::r#_language_dspecific_dlogic_dinternaldafny::_default::DefaultLanguageSpecificLogicConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient,
            > = valueOrError0.read().Extract();
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::TestRustClient(&::dafny_runtime::upcast_object::<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient, dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>()(client.clone()));
            return ();
        }
        pub fn TestRustClient(
            client: &::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>,
        ) -> () {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient::GetRuntimeInformation(::dafny_runtime::md!(client.clone())));
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !matches!(
                (&output.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            if !(output.read().value().language().clone()
                == ::dafny_runtime::string_utf16_of("Rust"))
            {
                panic!("Halt")
            };
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "Rust language: "
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(output.read().value().language())
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "; Rust runtime: "
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(output.read().value().runtime())
            );
            return ();
        }
        pub fn AllLanguageTests() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny::_default::LanguageSpecificLogic(&super::r#_language_dspecific_dlogic_dinternaldafny::_default::DefaultLanguageSpecificLogicConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient,
            > = valueOrError0.read().Extract();
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::TestAllLanguagesSuccess(&::dafny_runtime::upcast_object::<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient, dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>()(client.clone()));
            return ();
        }
        pub fn TestAllLanguagesSuccess(
            client: &::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>,
        ) -> () {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient::GetRuntimeInformation(::dafny_runtime::md!(client.clone())));
            output = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !matches!(
                (&output.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "Generic language: "
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(output.read().value().language())
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "; Generic runtime: "
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(output.read().value().runtime())
            );
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_LanguageSpecificLogicImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedLanguageSpecificLogicTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedRustOnlyTests() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default::WrappedLanguageSpecificLogic(&super::r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default::WrappedDefaultLanguageSpecificLogicConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient> = valueOrError0.read().Extract();
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::TestRustClient(&client);
            return ();
        }
        pub fn WrappedAllLanguageTests() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default::WrappedLanguageSpecificLogic(&super::r#_language_dspecific_dlogic_dinternaldafny_dwrapped::_default::WrappedDefaultLanguageSpecificLogicConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient> = valueOrError0.read().Extract();
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::TestAllLanguagesSuccess(
                &client,
            );
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedLanguageSpecificLogicTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"LanguageSpecificLogicImplTest.AllLanguageTests: "#
                ))
            );
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::AllLanguageTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"WrappedLanguageSpecificLogicTest.WrappedAllLanguageTests: "#
                ))
            );
            super::r#_WrappedLanguageSpecificLogicTest_Compile::_default::WrappedAllLanguageTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"RustLanguageSpecificLogicImplTest.RustSpecificTests: "#
                ))
            );
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::RustSpecificTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"RustLanguageSpecificLogicImplTest.AllLanguageTests: "#
                ))
            );
            super::r#_LanguageSpecificLogicImplTest_Compile::_default::AllLanguageTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"RustLanguageSpecificLogicTest.WrappedRustOnlyTests: "#
                ))
            );
            super::r#_WrappedLanguageSpecificLogicTest_Compile::_default::WrappedRustOnlyTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"RustLanguageSpecificLogicTest.WrappedAllLanguageTests: "#
                ))
            );
            super::r#_WrappedLanguageSpecificLogicTest_Compile::_default::WrappedAllLanguageTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::_module::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
fn main() {
    _module::_default::_Test__Main_();
}
