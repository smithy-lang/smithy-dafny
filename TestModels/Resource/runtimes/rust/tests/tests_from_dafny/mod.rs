#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
use simple_resources::implementation_from_dafny::*;

pub mod r#_Helpers_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn allNone(
        ) -> ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput>
        {
            ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput::GetResourceDataInput {
          blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::None {}),
          booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {}),
          stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {}),
          integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::None {}),
          longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::None {})
        })
        }
        pub fn checkMostNone(
            name: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            output: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
            >,
        ) -> () {
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Some {
                value: name.clone(),
            }) == output.stringValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<u8>,
            >::None {})
                == output.blobValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
                == output.booleanValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::None {})
                == output.integerValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::None {})
                == output.longValue().clone())
            {
                panic!("Halt")
            };
            return ();
        }
        pub fn allSome(
        ) -> ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput>
        {
            ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput::GetResourceDataInput {
          blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                value: ::dafny_runtime::seq![1]
              }),
          booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                value: true
              }),
          stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                value: ::dafny_runtime::string_utf16_of("Some")
              }),
          integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                value: 1
              }),
          longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                value: 1
              })
        })
        }
        pub fn checkSome(
            name: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            output: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
            >,
        ) -> () {
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Some {
                value: name.concat(&::dafny_runtime::string_utf16_of(" Some")),
            }) == output.stringValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<u8>,
            >::Some {
                value: ::dafny_runtime::seq![1],
            }) == output.blobValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                value: true,
            }) == output.booleanValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some { value: 1 })
                == output.integerValue().clone())
            {
                panic!("Halt")
            };
            if !(::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some { value: 1 })
                == output.longValue().clone())
            {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::r#_Helpers_Compile::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_SimpleResourcesTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestNoneGetData(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
            resource: &::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
            >,
        ) -> () {
            let mut input: ::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            > = super::r#_Helpers_Compile::_default::allNone();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource::GetResourceData(
                    ::dafny_runtime::md!(resource.clone()),
                    &input,
                ),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut result: ::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
            > = valueOrError0.read().Extract();
            super::r#_Helpers_Compile::_default::checkMostNone(config.name(), &result);
            return ();
        }
        pub fn TestSomeGetData(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
            resource: &::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
            >,
        ) -> () {
            let mut input: ::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            > = super::r#_Helpers_Compile::_default::allSome();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource::GetResourceData(
                    ::dafny_runtime::md!(resource.clone()),
                    &input,
                ),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut output: ::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
            > = valueOrError0.read().Extract();
            super::r#_Helpers_Compile::_default::checkSome(config.name(), &output);
            return ();
        }
        pub fn TestGetResources(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
            >,
        ) -> ::dafny_runtime::Object<
            dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
        > {
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
                >,
            >::new();
            let mut input: ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesInput> = ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesInput::GetResourcesInput {
            value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("Test")
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient::GetResources(::dafny_runtime::md!(client.clone()), &input));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut output: ::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
            > = valueOrError0.read().Extract();
            resource = ::dafny_runtime::MaybePlacebo::from(output.output().clone());
            return resource.read();
        }
        pub fn TestClient(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_simple_dresources_dinternaldafny::_default::SimpleResources(config),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
            > = valueOrError0.read().Extract();
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
                >,
            >::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
                >,
            >::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleResourcesTest_Compile::_default::TestGetResources(config, &::dafny_runtime::upcast_object::<super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient, dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient>()(client.clone())));
            resource = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            super::r#_SimpleResourcesTest_Compile::_default::TestNoneGetData(
                config,
                &resource.read(),
            );
            super::r#_SimpleResourcesTest_Compile::_default::TestSomeGetData(
                config,
                &resource.read(),
            );
            return ();
        }
        pub fn TestDefaultConfig() -> () {
            super::r#_SimpleResourcesTest_Compile::_default::TestClient(
                &super::r#_simple_dresources_dinternaldafny::_default::DefaultSimpleResourcesConfig(
                ),
            );
            return ();
        }
        pub fn TestCustomConfig() -> () {
            super::r#_SimpleResourcesTest_Compile::_default::TestClient(&::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig::SimpleResourcesConfig {
            name: ::dafny_runtime::string_utf16_of("Dafny")
          }));
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleResourcesTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_dresources_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleResourcesConfig(
        ) -> ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig>
        {
            super::r#_simple_dresources_dinternaldafny::_default::DefaultSimpleResourcesConfig()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dresources_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestWrappedClient(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dresources_dinternaldafny_dwrapped::_default::WrappedSimpleResources(config));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
            > = valueOrError0.read().Extract();
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
                >,
            >::new();
            let mut _out6 = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
                >,
            >::new();
            _out6 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleResourcesTest_Compile::_default::TestGetResources(config, &client),
            );
            resource = ::dafny_runtime::MaybePlacebo::from(_out6.read());
            super::r#_SimpleResourcesTest_Compile::_default::TestNoneGetData(
                config,
                &resource.read(),
            );
            super::r#_SimpleResourcesTest_Compile::_default::TestSomeGetData(
                config,
                &resource.read(),
            );
            return ();
        }
        pub fn WrappedTestDefaultConfig() -> () {
            super::r#_WrappedTest_Compile::_default::TestWrappedClient(&super::r#_simple_dresources_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleResourcesConfig());
            return ();
        }
        pub fn WrappedTestCustomConfig() -> () {
            super::r#_WrappedTest_Compile::_default::TestWrappedClient(&::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig::SimpleResourcesConfig {
            name: ::dafny_runtime::string_utf16_of("Dafny")
          }));
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::r#_WrappedTest_Compile::_default {
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
                    r#"SimpleResourcesTest.TestDefaultConfig: "#
                ))
            );
            super::r#_SimpleResourcesTest_Compile::_default::TestDefaultConfig();
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
                    r#"SimpleResourcesTest.TestCustomConfig: "#
                ))
            );
            super::r#_SimpleResourcesTest_Compile::_default::TestCustomConfig();
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
                    r#"WrappedTest.WrappedTestDefaultConfig: "#
                ))
            );
            super::r#_WrappedTest_Compile::_default::WrappedTestDefaultConfig();
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
                    r#"WrappedTest.WrappedTestCustomConfig: "#
                ))
            );
            super::r#_WrappedTest_Compile::_default::WrappedTestCustomConfig();
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
