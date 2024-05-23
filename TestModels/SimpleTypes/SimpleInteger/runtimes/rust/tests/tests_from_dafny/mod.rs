#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_SimpleIntegerImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetInteger() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dinteger_dinternaldafny::_default::SimpleInteger(&super::r#_simple_dtypes_dinteger_dinternaldafny::_default::DefaultSimpleIntegerConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetInteger(&::dafny_runtime::upcast_object::<super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient, dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>()(client.clone()));
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetIntegerKnownValue(&::dafny_runtime::upcast_object::<super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient, dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>()(client.clone()));
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetIntegerEdgeCases(&::dafny_runtime::upcast_object::<super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient, dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>()(client.clone()));
            return ();
        }
        pub fn TestGetInteger(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient::GetInteger(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput::GetIntegerInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                      value: 1
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&0) == 1) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetIntegerKnownValue(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient::GetIntegerKnownValueTest(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput::GetIntegerInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                      value: 20
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&0) == 20) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetIntegerEdgeCases(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>,
        ) -> () {
            let mut inputInteger: ::dafny_runtime::Sequence<i32> = ::dafny_runtime::seq![
                -1,
                0,
                1,
                ::dafny_runtime::truncate!(
                    super::r#_StandardLibrary_Compile_dUInt_Compile::_default::INT32_MAX_LIMIT()
                        - ::dafny_runtime::int!(1),
                    i32
                ),
                0 - ::dafny_runtime::truncate!(
                    super::r#_StandardLibrary_Compile_dUInt_Compile::_default::INT32_MAX_LIMIT()
                        - ::dafny_runtime::int!(1),
                    i32
                )
            ];
            let mut _hi0: ::dafny_runtime::DafnyInt = inputInteger.cardinality();
            for i in ::dafny_runtime::integer_range(::dafny_runtime::int!(0), _hi0.clone()) {
                let mut integerValue: i32 = inputInteger.get(&i);
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&integerValue));
                let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
                let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
                _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient::GetInteger(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput::GetIntegerInput {
                  value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                        value: integerValue
                      })
                })));
                valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
                if !(!valueOrError0.read().IsFailure()) {
                    panic!("Halt")
                };
                let mut ret: ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                > = valueOrError0.read().Extract();
                if !(ret.value().UnwrapOr(&0) == integerValue) {
                    panic!("Halt")
                };
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret))
            }
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleIntegerImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_dtypes_dinteger_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleIntegerConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::SimpleIntegerConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::SimpleIntegerConfig::SimpleIntegerConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dtypes_dinteger_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleTypesIntegerTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetInteger() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dinteger_dinternaldafny_dwrapped::_default::WrappedSimpleInteger(&super::r#_simple_dtypes_dinteger_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleIntegerConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient> = valueOrError0.read().Extract();
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetInteger(&client);
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetIntegerKnownValue(&client);
            super::r#_SimpleIntegerImplTest_Compile::_default::TestGetIntegerEdgeCases(&client);
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleTypesIntegerTest_Compile::_default
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
                    r#"SimpleIntegerImplTest.GetInteger: "#
                ))
            );
            super::r#_SimpleIntegerImplTest_Compile::_default::GetInteger();
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
                    r#"WrappedSimpleTypesIntegerTest.GetInteger: "#
                ))
            );
            super::r#_WrappedSimpleTypesIntegerTest_Compile::_default::GetInteger();
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
