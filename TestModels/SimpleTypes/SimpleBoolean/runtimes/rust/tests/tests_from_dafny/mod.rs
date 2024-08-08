#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod simple {
    pub mod types {
        pub mod boolean {
            pub mod internaldafny {
                pub mod wrapped {
                    pub struct _default {}

                    impl _default {
                        pub fn WrappedDefaultSimpleBooleanConfig() -> ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::SimpleBooleanConfig>{
                            ::std::rc::Rc::new(crate::simple::types::boolean::internaldafny::types::SimpleBooleanConfig::SimpleBooleanConfig {})
                        }
                    }
                }
            }
        }
    }
}
pub mod r#_SimpleBooleanImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn GetBooleanTrue() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::_default::SimpleBoolean(&crate::simple::types::boolean::internaldafny::_default::DefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
            > = valueOrError0.read().Extract();
            crate::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&::dafny_runtime::upcast_object::<crate::simple::types::boolean::internaldafny::SimpleBooleanClient, dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>()(client.clone()));
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::_default::SimpleBoolean(&crate::simple::types::boolean::internaldafny::_default::DefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                crate::simple::types::boolean::internaldafny::SimpleBooleanClient,
            > = valueOrError0.read().Extract();
            crate::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&::dafny_runtime::upcast_object::<crate::simple::types::boolean::internaldafny::SimpleBooleanClient, dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>()(client.clone()));
            return ();
        }
        pub fn TestGetBooleanTrue(
            client: &::dafny_runtime::Object<
                dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient::GetBoolean(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(crate::simple::types::boolean::internaldafny::types::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: true
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
            > = valueOrError0.read().Extract();
            let mut _e00: bool = ret.value().UnwrapOr(&false);
            let mut _e10: bool = true;
            if !(_e00 == _e10) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e00));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e10));
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetBooleanFalse(
            client: &::dafny_runtime::Object<
                dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient::GetBoolean(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(crate::simple::types::boolean::internaldafny::types::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: false
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                crate::simple::types::boolean::internaldafny::types::GetBooleanOutput,
            > = valueOrError0.read().Extract();
            let mut _e01: bool = ret.value().UnwrapOr(&true);
            let mut _e11: bool = false;
            if !(_e01 == _e11) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e01));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e11));
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
    }
}
pub mod r#_WrappedSimpleTypesBooleanTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn GetBooleanTrue() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>, ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>, ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::wrapped::_default::WrappedSimpleBoolean(&crate::simple::types::boolean::internaldafny::wrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient,
            > = valueOrError0.read().Extract();
            crate::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&client);
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>, ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient>, ::std::rc::Rc<crate::simple::types::boolean::internaldafny::types::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(crate::simple::types::boolean::internaldafny::wrapped::_default::WrappedSimpleBoolean(&crate::simple::types::boolean::internaldafny::wrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn crate::simple::types::boolean::internaldafny::types::ISimpleTypesBooleanClient,
            > = valueOrError0.read().Extract();
            crate::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&client);
            return ();
        }
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"SimpleBooleanImplTest.GetBooleanTrue: "#
                ))
            );
            crate::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanTrue();
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
            crate::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanFalse();
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
            crate::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanTrue();
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
            crate::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanFalse();
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
}
fn main() {
    _module::_default::_Test__Main_();
}
