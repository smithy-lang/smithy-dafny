#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_simple_dconstructor_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleConstructorConfig() -> ::std::rc::Rc<
            super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig,
        > {
            super::r#_simple_dconstructor_dinternaldafny::_default::DefaultSimpleConstructorConfig()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dconstructor_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_SimpleConstructorImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestGetConstructorWithDefaultConfig() -> () {
            let mut expectedOutput: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput::GetConstructorOutput {
            internalConfigString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("inputString")
                }),
            blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                  value: ::dafny_runtime::seq![0]
                }),
            booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                  value: false
                }),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("")
                }),
            integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                  value: 0
                }),
            longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                  value: 0
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dconstructor_dinternaldafny::_default::SimpleConstructor(&super::r#_simple_dconstructor_dinternaldafny::_default::DefaultSimpleConstructorConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructor(&::dafny_runtime::upcast_object::<super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient, dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>()(client.clone()), &expectedOutput);
            return ();
        }
        pub fn TestGetConstructorWithParamConfig() -> () {
            let mut paramConfig: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig::SimpleConstructorConfig {
            blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                  value: ::dafny_runtime::seq![0, 0, 7]
                }),
            booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                  value: true
                }),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("ParamString")
                }),
            integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                  value: 7
                }),
            longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                  value: 7
                })
          });
            let mut expectedOutput: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput::GetConstructorOutput {
            internalConfigString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("inputString")
                }),
            blobValue: paramConfig.blobValue().clone(),
            booleanValue: paramConfig.booleanValue().clone(),
            stringValue: paramConfig.stringValue().clone(),
            integerValue: paramConfig.integerValue().clone(),
            longValue: paramConfig.longValue().clone()
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_simple_dconstructor_dinternaldafny::_default::SimpleConstructor(
                    &paramConfig,
                ),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructor(&::dafny_runtime::upcast_object::<super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient, dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>()(client.clone()), &expectedOutput);
            return ();
        }
        pub fn TestGetConstructor(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient,
            >,
            expectedOutput: &::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
            >,
        ) -> () {
            let mut input: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput::GetConstructorInput {
            value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("inputString")
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient::GetConstructor(::dafny_runtime::md!(client.clone()), &input));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
            > = valueOrError0.read().Extract();
            if !(ret.internalConfigString().clone()
                == expectedOutput.internalConfigString().clone())
            {
                panic!("Halt")
            };
            if !(ret.blobValue().clone() == expectedOutput.blobValue().clone()) {
                panic!("Halt")
            };
            if !(ret.booleanValue().clone() == expectedOutput.booleanValue().clone()) {
                panic!("Halt")
            };
            if !(ret.stringValue().clone() == expectedOutput.stringValue().clone()) {
                panic!("Halt")
            };
            if !(ret.integerValue().clone() == expectedOutput.integerValue().clone()) {
                panic!("Halt")
            };
            if !(ret.longValue().clone() == expectedOutput.longValue().clone()) {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleConstructorImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleConstructorTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestGetConstructorWithParamConfig() -> () {
            let mut paramConfig: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig::SimpleConstructorConfig {
            blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                  value: ::dafny_runtime::seq![0, 0, 7]
                }),
            booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                  value: true
                }),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("ParamString")
                }),
            integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                  value: 7
                }),
            longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                  value: 7
                })
          });
            let mut expectedOutput: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput::GetConstructorOutput {
            internalConfigString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("inputString")
                }),
            blobValue: paramConfig.blobValue().clone(),
            booleanValue: paramConfig.booleanValue().clone(),
            stringValue: paramConfig.stringValue().clone(),
            integerValue: paramConfig.integerValue().clone(),
            longValue: paramConfig.longValue().clone()
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dconstructor_dinternaldafny_dwrapped::_default::WrappedSimpleConstructor(&paramConfig));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructor(
                &client,
                &expectedOutput,
            );
            return ();
        }
        pub fn TestGetConstructorWithDefaultConfig() -> () {
            let mut expectedOutput: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput::GetConstructorOutput {
            internalConfigString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("inputString")
                }),
            blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                  value: ::dafny_runtime::seq![0]
                }),
            booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                  value: false
                }),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("")
                }),
            integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                  value: 0
                }),
            longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                  value: 0
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dconstructor_dinternaldafny_dwrapped::_default::WrappedSimpleConstructor(&super::r#_simple_dconstructor_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleConstructorConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructor(
                &client,
                &expectedOutput,
            );
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleConstructorTest_Compile::_default
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
                    r#"SimpleConstructorImplTest.TestGetConstructorWithDefaultConfig: "#
                ))
            );
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructorWithDefaultConfig();
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
                    r#"SimpleConstructorImplTest.TestGetConstructorWithParamConfig: "#
                ))
            );
            super::r#_SimpleConstructorImplTest_Compile::_default::TestGetConstructorWithParamConfig();
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
                    r#"WrappedSimpleConstructorTest.TestGetConstructorWithParamConfig: "#
                ))
            );
            super::r#_WrappedSimpleConstructorTest_Compile::_default::TestGetConstructorWithParamConfig();
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
                    r#"WrappedSimpleConstructorTest.TestGetConstructorWithDefaultConfig: "#
                ))
            );
            super::r#_WrappedSimpleConstructorTest_Compile::_default::TestGetConstructorWithDefaultConfig();
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
