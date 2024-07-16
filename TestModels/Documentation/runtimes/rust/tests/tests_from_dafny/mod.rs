#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_SimpleDocumentationImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestClient() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_simple_ddocumentation_dinternaldafny::SimpleDocumentationClient>, ::std::rc::Rc<super::r#_simple_ddocumentation_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_simple_ddocumentation_dinternaldafny::SimpleDocumentationClient>, ::std::rc::Rc<super::r#_simple_ddocumentation_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_ddocumentation_dinternaldafny::_default::SimpleDocumentation(&super::r#_simple_ddocumentation_dinternaldafny::_default::DefaultSimpleDocumentationConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_ddocumentation_dinternaldafny::SimpleDocumentationClient,
            > = valueOrError0.read().Extract();
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleDocumentationImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_ddocumentation_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleDocumentationConfig() -> ::std::rc::Rc<
            super::r#_simple_ddocumentation_dinternaldafny_dtypes::SimpleDocumentationConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_ddocumentation_dinternaldafny_dtypes::SimpleDocumentationConfig::SimpleDocumentationConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_ddocumentation_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleDocumentationTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetString() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_ddocumentation_dinternaldafny_dtypes::ISimpleDocumentationClient>, ::std::rc::Rc<super::r#_simple_ddocumentation_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_ddocumentation_dinternaldafny_dtypes::ISimpleDocumentationClient>, ::std::rc::Rc<super::r#_simple_ddocumentation_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_ddocumentation_dinternaldafny_dwrapped::_default::WrappedSimpleDocumentation(&super::r#_simple_ddocumentation_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleDocumentationConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_simple_ddocumentation_dinternaldafny_dtypes::ISimpleDocumentationClient> = valueOrError0.read().Extract();
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleDocumentationTest_Compile::_default
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
                    r#"SimpleDocumentationImplTest.TestClient: "#
                ))
            );
            super::r#_SimpleDocumentationImplTest_Compile::_default::TestClient();
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
                    r#"WrappedSimpleDocumentationTest.GetString: "#
                ))
            );
            super::r#_WrappedSimpleDocumentationTest_Compile::_default::GetString();
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
