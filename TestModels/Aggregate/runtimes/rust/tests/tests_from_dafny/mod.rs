#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_SimpleAggregateImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetAggregate() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_daggregate_dinternaldafny::_default::SimpleAggregate(&super::r#_simple_daggregate_dinternaldafny::_default::DefaultSimpleAggregateConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleAggregateImplTest_Compile::_default::TestGetAggregate(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >()(client.clone()),
            );
            super::r#_SimpleAggregateImplTest_Compile::_default::TestGetAggregateKnownValue(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >()(client.clone()),
            );
            return ();
        }
        pub fn TestGetAggregate(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
            >,
        ) -> () {
            let mut stringList: ::dafny_runtime::Sequence<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::seq![::dafny_runtime::string_utf16_of("Test")];
            let mut simpleStringMap: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test1")) => (::dafny_runtime::string_utf16_of("Success"))];
            let mut structureList: ::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>> = ::dafny_runtime::seq![::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
              stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                    value: ::dafny_runtime::string_utf16_of("Test2")
                  }),
              integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                    value: 2
                  })
            })];
            let mut simpleIntegerMap: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                i32,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test3")) => (3)];
            let mut nestedStructure: ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure> = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
            stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                  value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                        value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                              value: ::dafny_runtime::string_utf16_of("Nested")
                            })
                      })
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient::GetAggregate(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput::GetAggregateInput {
                simpleStringList: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::Some {
                      value: stringList.clone()
                    }),
                structureList: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>>>::Some {
                      value: structureList.clone()
                    }),
                simpleStringMap: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::Some {
                      value: simpleStringMap.clone()
                    }),
                simpleIntegerMap: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32>>::Some {
                      value: simpleIntegerMap.clone()
                    }),
                nestedStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure>>::Some {
                      value: nestedStructure.clone()
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
            > = valueOrError0.read().Extract();
            if !(ret.simpleStringList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >),
            ) == stringList.clone())
            {
                panic!("Halt")
            };
            if !(ret.structureList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                        >,
                    >),
            ) == structureList.clone())
            {
                panic!("Halt")
            };
            if !(ret.simpleStringMap().UnwrapOr(&::dafny_runtime::map![])
                == simpleStringMap.clone())
            {
                panic!("Halt")
            };
            if !(ret.simpleIntegerMap().UnwrapOr(&::dafny_runtime::map![])
                == simpleIntegerMap.clone())
            {
                panic!("Halt")
            };
            if !(ret.nestedStructure().UnwrapOr(&::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
              stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                    value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                          value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                                value: ::dafny_runtime::string_utf16_of("")
                              })
                        })
                  })
            })) == nestedStructure.clone()) {
        panic!("Halt")
      };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetAggregateKnownValue(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
            >,
        ) -> () {
            let mut stringList: ::dafny_runtime::Sequence<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::seq![::dafny_runtime::string_utf16_of("Test")];
            let mut simpleStringMap: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test1")) => (::dafny_runtime::string_utf16_of("Success"))];
            let mut structureList: ::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>> = ::dafny_runtime::seq![::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
              stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                    value: ::dafny_runtime::string_utf16_of("Test2")
                  }),
              integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                    value: 2
                  })
            })];
            let mut simpleIntegerMap: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                i32,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test3")) => (3)];
            let mut nestedStructure: ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure> = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
            stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                  value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                        value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                              value: ::dafny_runtime::string_utf16_of("Nested")
                            })
                      })
                })
          });
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient::GetAggregate(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput::GetAggregateInput {
                simpleStringList: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::Some {
                      value: stringList.clone()
                    }),
                structureList: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>>>::Some {
                      value: structureList.clone()
                    }),
                simpleStringMap: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::Some {
                      value: simpleStringMap.clone()
                    }),
                simpleIntegerMap: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32>>::Some {
                      value: simpleIntegerMap.clone()
                    }),
                nestedStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure>>::Some {
                      value: nestedStructure.clone()
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
            > = valueOrError0.read().Extract();
            if !(ret.simpleStringList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >),
            ) == stringList.clone())
            {
                panic!("Halt")
            };
            if !(ret.structureList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                        >,
                    >),
            ) == structureList.clone())
            {
                panic!("Halt")
            };
            if !(ret.simpleStringMap().UnwrapOr(&::dafny_runtime::map![])
                == simpleStringMap.clone())
            {
                panic!("Halt")
            };
            if !(ret.simpleIntegerMap().UnwrapOr(&::dafny_runtime::map![])
                == simpleIntegerMap.clone())
            {
                panic!("Halt")
            };
            if !(ret.nestedStructure().UnwrapOr(&::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
              stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                    value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                          value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                                value: ::dafny_runtime::string_utf16_of("")
                              })
                        })
                  })
            })) == nestedStructure.clone()) {
        panic!("Halt")
      };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleAggregateImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_daggregate_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleAggregateConfig(
        ) -> ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::SimpleAggregateConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::SimpleAggregateConfig::SimpleAggregateConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_daggregate_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleTypesStringTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetAggregate() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient>, ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient>, ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_daggregate_dinternaldafny_dwrapped::_default::WrappedSimpleAggregate(&super::r#_simple_daggregate_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleAggregateConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleAggregateImplTest_Compile::_default::TestGetAggregate(&client);
            super::r#_SimpleAggregateImplTest_Compile::_default::TestGetAggregateKnownValue(
                &client,
            );
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleTypesStringTest_Compile::_default
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
                    r#"SimpleAggregateImplTest.GetAggregate: "#
                ))
            );
            super::r#_SimpleAggregateImplTest_Compile::_default::GetAggregate();
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
                    r#"WrappedSimpleTypesStringTest.GetAggregate: "#
                ))
            );
            super::r#_WrappedSimpleTypesStringTest_Compile::_default::GetAggregate();
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
