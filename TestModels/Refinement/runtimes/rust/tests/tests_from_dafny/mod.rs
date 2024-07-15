#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_SimpleRefinementImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn Refinement() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny::_default::SimpleRefinement(&super::r#_simple_drefinement_dinternaldafny::_default::DefaultSimpleRefinementConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleRefinementImplTest_Compile::_default::TestGetRefinement(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >()(client.clone()),
            );
            super::r#_SimpleRefinementImplTest_Compile::_default::TestOnlyInput(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >()(client.clone()),
            );
            super::r#_SimpleRefinementImplTest_Compile::_default::TestOnlyOutput(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >()(client.clone()),
            );
            super::r#_SimpleRefinementImplTest_Compile::_default::TestReadonlyOperation(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >()(client.clone()),
            );
            return ();
        }
        pub fn TestGetRefinement(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient::GetRefinement(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementInput::GetRefinementInput {
                requiredString: ::dafny_runtime::string_utf16_of("GetRefinement"),
                optionalString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                      value: ::dafny_runtime::string_utf16_of("GetRefinementOptional")
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
            > = valueOrError0.read().Extract();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&res));
            if !(res.requiredString().clone() == ::dafny_runtime::string_utf16_of("GetRefinement"))
            {
                panic!("Halt")
            };
            if !(res
                .optionalString()
                .UnwrapOr(&::dafny_runtime::string_utf16_of(""))
                == ::dafny_runtime::string_utf16_of("GetRefinementOptional"))
            {
                panic!("Halt")
            };
            return ();
        }
        pub fn TestOnlyInput(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient::OnlyInput(::dafny_runtime::md!(client.clone()), &::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyInputInput::OnlyInputInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                      value: ::dafny_runtime::string_utf16_of("InputValue")
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut res: () = valueOrError0.read().Extract();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&res));
            return ();
        }
        pub fn TestOnlyOutput(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient::OnlyOutput(::dafny_runtime::md!(client.clone())));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
            > = valueOrError0.read().Extract();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&res));
            if !(res.value().UnwrapOr(&::dafny_runtime::string_utf16_of(""))
                == ::dafny_runtime::string_utf16_of("Hello World"))
            {
                panic!("Halt")
            };
            return ();
        }
        pub fn TestReadonlyOperation(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            >,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput>, ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>>>>::new();
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient::ReadonlyOperation(::dafny_runtime::rd!(client.clone()), &::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationInput::ReadonlyOperationInput {
                requiredString: ::dafny_runtime::string_utf16_of("Readonly"),
                optionalString: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                      value: ::dafny_runtime::string_utf16_of("ReadonlyOptional")
                    })
              })));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput,
            > = valueOrError0.read().Extract();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&res));
            if !(res.requiredString().clone() == ::dafny_runtime::string_utf16_of("Readonly")) {
                panic!("Halt")
            };
            if !(res
                .optionalString()
                .UnwrapOr(&::dafny_runtime::string_utf16_of(""))
                == ::dafny_runtime::string_utf16_of("ReadonlyOptional"))
            {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleRefinementImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_drefinement_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleRefinementConfig(
        ) -> ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::SimpleRefinementConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::SimpleRefinementConfig::SimpleRefinementConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_drefinement_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleRefinementTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn Refinement() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient>, ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient>, ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_drefinement_dinternaldafny_dwrapped::_default::WrappedSimpleRefinement(&super::r#_simple_drefinement_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleRefinementConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleRefinementImplTest_Compile::_default::TestGetRefinement(&client);
            super::r#_SimpleRefinementImplTest_Compile::_default::TestOnlyInput(&client);
            super::r#_SimpleRefinementImplTest_Compile::_default::TestOnlyOutput(&client);
            super::r#_SimpleRefinementImplTest_Compile::_default::TestReadonlyOperation(&client);
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleRefinementTest_Compile::_default
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
                    r#"SimpleRefinementImplTest.Refinement: "#
                ))
            );
            super::r#_SimpleRefinementImplTest_Compile::_default::Refinement();
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
                    r#"WrappedSimpleRefinementTest.Refinement: "#
                ))
            );
            super::r#_WrappedSimpleRefinementTest_Compile::_default::Refinement();
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
