#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_simple_dtypes_dboolean_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleBooleanConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig::SimpleBooleanConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_SimpleBooleanImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetBooleanTrue() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny::_default::SimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny::_default::DefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&::dafny_runtime::upcast_object::<super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient, dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>()(client.clone()));
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny::_default::SimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny::_default::DefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&::dafny_runtime::upcast_object::<super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient, dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>()(client.clone()));
            return ();
        }
        pub fn TestGetBooleanTrue(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient::GetBoolean(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: true
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&false) == true) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetBooleanFalse(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient::GetBoolean(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: false
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&true) == false) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleBooleanImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleTypesBooleanTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetBooleanTrue() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedSimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient> = valueOrError0.read().Extract();
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&client);
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedSimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient> = valueOrError0.read().Extract();
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&client);
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleTypesBooleanTest_Compile::_default
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
                    r#"SimpleBooleanImplTest.GetBooleanTrue: "#
                ))
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanTrue();
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
                    r#"SimpleBooleanImplTest.GetBooleanFalse: "#
                ))
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanFalse();
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
                    r#"WrappedSimpleTypesBooleanTest.GetBooleanTrue: "#
                ))
            );
            super::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanTrue();
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
                    r#"WrappedSimpleTypesBooleanTest.GetBooleanFalse: "#
                ))
            );
            super::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanFalse();
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
