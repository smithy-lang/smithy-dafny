#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_SimpleBlobImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetBlob() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dblob_dinternaldafny::SimpleBlobClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dblob_dinternaldafny::SimpleBlobClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dblob_dinternaldafny::_default::SimpleBlob(&super::r#_simple_dtypes_dblob_dinternaldafny::_default::DefaultSimpleBlobConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                super::r#_simple_dtypes_dblob_dinternaldafny::SimpleBlobClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleBlobImplTest_Compile::_default::TestGetBlob(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_dtypes_dblob_dinternaldafny::SimpleBlobClient,
                    dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient,
                >()(client.clone()),
            );
            super::r#_SimpleBlobImplTest_Compile::_default::TestGetBlobKnownValueTest(
                &::dafny_runtime::upcast_object::<
                    super::r#_simple_dtypes_dblob_dinternaldafny::SimpleBlobClient,
                    dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient,
                >()(client.clone()),
            );
            return ();
        }
        pub fn TestGetBlob(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient,
            >,
        ) -> () {
            let mut s: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![0, 1, 2];
            let mut convertedBlobInput: ::std::rc::Rc<
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobInput,
            > = ::std::rc::Rc::new(
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobInput::GetBlobInput {
                    value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                        ::dafny_runtime::Sequence<u8>,
                    >::Some {
                        value: s.clone(),
                    }),
                },
            );
            super::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(
                convertedBlobInput.value().value(),
            );
            if !(convertedBlobInput.value().value().clone() == s.clone()) {
                panic!("Halt")
            };
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient::GetBlob(::dafny_runtime::md!(client.clone()), &convertedBlobInput));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&::dafny_runtime::seq![0])
                == convertedBlobInput.value().value().clone())
            {
                panic!("Halt")
            };
            if !(ret.value().UnwrapOr(&::dafny_runtime::seq![0]) == s.clone()) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
        pub fn TestGetBlobKnownValueTest(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient,
            >,
        ) -> () {
            let mut s: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![0, 2, 4];
            let mut convertedBlobInput: ::std::rc::Rc<
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobInput,
            > = ::std::rc::Rc::new(
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobInput::GetBlobInput {
                    value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                        ::dafny_runtime::Sequence<u8>,
                    >::Some {
                        value: s.clone(),
                    }),
                },
            );
            super::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(
                convertedBlobInput.value().value(),
            );
            if !(convertedBlobInput.value().value().clone() == s.clone()) {
                panic!("Halt")
            };
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient::GetBlobKnownValueTest(::dafny_runtime::md!(client.clone()), &convertedBlobInput));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut ret: ::std::rc::Rc<
                super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::GetBlobOutput,
            > = valueOrError0.read().Extract();
            if !(ret.value().UnwrapOr(&::dafny_runtime::seq![0])
                == convertedBlobInput.value().value().clone())
            {
                panic!("Halt")
            };
            if !(ret.value().UnwrapOr(&::dafny_runtime::seq![0]) == s.clone()) {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret));
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleBlobImplTest_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_simple_dtypes_dblob_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn WrappedDefaultSimpleBlobConfig(
        ) -> ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::SimpleBlobConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::SimpleBlobConfig::SimpleBlobConfig {})
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dtypes_dblob_dinternaldafny_dwrapped::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod r#_WrappedSimpleTypesBlobTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetBlob() -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient>, ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient>, ::std::rc::Rc<super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dblob_dinternaldafny_dwrapped::_default::WrappedSimpleBlob(&super::r#_simple_dtypes_dblob_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleBlobConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<
                dyn super::r#_simple_dtypes_dblob_dinternaldafny_dtypes::ISimpleTypesBlobClient,
            > = valueOrError0.read().Extract();
            super::r#_SimpleBlobImplTest_Compile::_default::TestGetBlob(&client);
            super::r#_SimpleBlobImplTest_Compile::_default::TestGetBlobKnownValueTest(&client);
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_WrappedSimpleTypesBlobTest_Compile::_default
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
                    r#"SimpleBlobImplTest.GetBlob: "#
                ))
            );
            super::r#_SimpleBlobImplTest_Compile::_default::GetBlob();
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
                    r#"WrappedSimpleTypesBlobTest.GetBlob: "#
                ))
            );
            super::r#_WrappedSimpleTypesBlobTest_Compile::_default::GetBlob();
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
