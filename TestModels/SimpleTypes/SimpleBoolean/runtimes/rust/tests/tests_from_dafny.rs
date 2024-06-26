#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
use simple_boolean::implementation_from_dafny::*;
use simple_boolean::*;
mod _wrapped;
pub mod r#_simple_dtypes_dboolean_dinternaldafny_dwrapped {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn WrappedDefaultSimpleBooleanConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::SimpleBooleanConfig::SimpleBooleanConfig {})
        }
    }
}
pub mod r#_SimpleBooleanImplTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetBooleanTrue() -> () {
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                >,
            >::new();
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
            client = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract().clone(), /* <i>Coercion from T to ::dafny_runtime::Object<super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient></i> not yet implemented */
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>>::upcast_to(client.read()));
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient,
                >,
            >::new();
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
            client = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract().clone(), /* <i>Coercion from T to ::dafny_runtime::Object<super::r#_simple_dtypes_dboolean_dinternaldafny::SimpleBooleanClient></i> not yet implemented */
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>>::upcast_to(client.read()));
            return ();
        }
        pub fn TestGetBooleanTrue(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
        ) -> () {
            let mut ret = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput,
                >,
            >::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(::dafny_runtime::md!(client.clone()).GetBoolean(&::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: true
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            ret = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput></i> not yet implemented */
            );
            if !((ret.read().value().UnwrapOr(
                &false, /* <i>Coercion from bool to T</i> not yet implemented */
            )/* <i>Coercion from T to bool</i> not yet implemented */)
                == true)
            {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret.read()));
            return ();
        }
        pub fn TestGetBooleanFalse(
            client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>,
        ) -> () {
            let mut ret = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput,
                >,
            >::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(::dafny_runtime::md!(client.clone()).GetBoolean(&::std::rc::Rc::new(super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanInput::GetBooleanInput {
                value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                      value: false
                    })
              })));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            ret = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::GetBooleanOutput></i> not yet implemented */
            );
            if !((ret.read().value().UnwrapOr(
                &true, /* <i>Coercion from bool to T</i> not yet implemented */
            )/* <i>Coercion from T to bool</i> not yet implemented */)
                == false)
            {
                panic!("Halt")
            };
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(&ret.read()));
            return ();
        }
    }
}
pub mod r#_WrappedSimpleTypesBooleanTest_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetBooleanTrue() -> () {
            let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedSimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            client = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract().clone(), /* <i>Coercion from T to ::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient></i> not yet implemented */
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanTrue(&client.read());
            return ();
        }
        pub fn GetBooleanFalse() -> () {
            let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient>, ::std::rc::Rc<super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedSimpleBoolean(&super::r#_simple_dtypes_dboolean_dinternaldafny_dwrapped::_default::WrappedDefaultSimpleBooleanConfig()));
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            client = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract().clone(), /* <i>Coercion from T to ::dafny_runtime::Object<dyn super::r#_simple_dtypes_dboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient></i> not yet implemented */
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::TestGetBooleanFalse(&client.read());
            return ();
        }
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            success = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "SimpleBooleanImplTest.GetBooleanTrue: "
                ))
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanTrue();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "PASSED
"
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "SimpleBooleanImplTest.GetBooleanFalse: "
                ))
            );
            super::r#_SimpleBooleanImplTest_Compile::_default::GetBooleanFalse();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "PASSED
"
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "WrappedSimpleTypesBooleanTest.GetBooleanTrue: "
                ))
            );
            super::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanTrue();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "PASSED
"
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "WrappedSimpleTypesBooleanTest.GetBooleanFalse: "
                ))
            );
            super::r#_WrappedSimpleTypesBooleanTest_Compile::_default::GetBooleanFalse();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    "PASSED
"
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
