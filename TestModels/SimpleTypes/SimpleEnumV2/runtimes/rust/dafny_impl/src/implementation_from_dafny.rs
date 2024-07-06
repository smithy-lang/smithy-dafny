#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_denumv2_dinternaldafny_dtypes {
    #[derive(PartialEq, Clone)]
    pub enum DafnyCallEvent<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> {
        DafnyCallEvent { input: I, output: O },
        _PhantomVariant(::std::marker::PhantomData<I>, ::std::marker::PhantomData<O>),
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> DafnyCallEvent<I, O> {
        pub fn input(&self) -> &I {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => input,
                DafnyCallEvent::_PhantomVariant(..) => panic!(),
            }
        }
        pub fn output(&self) -> &O {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => output,
                DafnyCallEvent::_PhantomVariant(..) => panic!(),
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::std::fmt::Debug
        for DafnyCallEvent<I, O>
    {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::dafny_runtime::DafnyPrint
        for DafnyCallEvent<I, O>
    {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => {
                    write!(_formatter, "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                DafnyCallEvent::_PhantomVariant(..) => {
                    panic!()
                }
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType + Eq, O: ::dafny_runtime::DafnyType + Eq> Eq
        for DafnyCallEvent<I, O>
    {
    }

    impl<
            I: ::dafny_runtime::DafnyType + ::std::hash::Hash,
            O: ::dafny_runtime::DafnyType + ::std::hash::Hash,
        > ::std::hash::Hash for DafnyCallEvent<I, O>
    {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => {
                    input.hash(_state);
                    output.hash(_state)
                }
                DafnyCallEvent::_PhantomVariant(..) => {
                    panic!()
                }
            }
        }
    }

    impl<
            I: ::dafny_runtime::DafnyType + ::std::default::Default,
            O: ::dafny_runtime::DafnyType + ::std::default::Default,
        > ::std::default::Default for DafnyCallEvent<I, O>
    {
        fn default() -> DafnyCallEvent<I, O> {
            DafnyCallEvent::DafnyCallEvent {
                input: ::std::default::Default::default(),
                output: ::std::default::Default::default(),
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType>
        ::std::convert::AsRef<DafnyCallEvent<I, O>> for &DafnyCallEvent<I, O>
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetEnumV2Input {
        GetEnumV2Input {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape,
                    >,
                >,
            >,
        },
    }

    impl GetEnumV2Input {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape,
                >,
            >,
        > {
            match self {
                GetEnumV2Input::GetEnumV2Input { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetEnumV2Input {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetEnumV2Input {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetEnumV2Input::GetEnumV2Input { value } => {
                    write!(_formatter, "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.GetEnumV2Input.GetEnumV2Input(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetEnumV2Input {}

    impl ::std::hash::Hash for GetEnumV2Input {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetEnumV2Input::GetEnumV2Input { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetEnumV2Input {
        fn default() -> GetEnumV2Input {
            GetEnumV2Input::GetEnumV2Input {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetEnumV2Input> for &GetEnumV2Input {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetEnumV2Output {
        GetEnumV2Output {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape,
                    >,
                >,
            >,
        },
    }

    impl GetEnumV2Output {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape,
                >,
            >,
        > {
            match self {
                GetEnumV2Output::GetEnumV2Output { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetEnumV2Output {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetEnumV2Output {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetEnumV2Output::GetEnumV2Output { value } => {
                    write!(_formatter, "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.GetEnumV2Output.GetEnumV2Output(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetEnumV2Output {}

    impl ::std::hash::Hash for GetEnumV2Output {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetEnumV2Output::GetEnumV2Output { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetEnumV2Output {
        fn default() -> GetEnumV2Output {
            GetEnumV2Output::GetEnumV2Output {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetEnumV2Output> for &GetEnumV2Output {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleEnumV2Config {
        SimpleEnumV2Config {},
    }

    impl SimpleEnumV2Config {}

    impl ::std::fmt::Debug for SimpleEnumV2Config {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleEnumV2Config {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleEnumV2Config::SimpleEnumV2Config {} => {
                    write!(_formatter, "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.SimpleEnumV2Config.SimpleEnumV2Config")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleEnumV2Config {}

    impl ::std::hash::Hash for SimpleEnumV2Config {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleEnumV2Config::SimpleEnumV2Config {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleEnumV2Config {
        fn default() -> SimpleEnumV2Config {
            SimpleEnumV2Config::SimpleEnumV2Config {}
        }
    }

    impl ::std::convert::AsRef<SimpleEnumV2Config> for &SimpleEnumV2Config {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleEnumV2Shape {
        FIRST {},
        SECOND {},
        THIRD {},
    }

    impl SimpleEnumV2Shape {}

    impl ::std::fmt::Debug for SimpleEnumV2Shape {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleEnumV2Shape {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleEnumV2Shape::FIRST {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.SimpleEnumV2Shape.FIRST"
                    )?;
                    Ok(())
                }
                SimpleEnumV2Shape::SECOND {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.SimpleEnumV2Shape.SECOND"
                    )?;
                    Ok(())
                }
                SimpleEnumV2Shape::THIRD {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.SimpleEnumV2Shape.THIRD"
                    )?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleEnumV2Shape {}

    impl ::std::hash::Hash for SimpleEnumV2Shape {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleEnumV2Shape::FIRST {} => {}
                SimpleEnumV2Shape::SECOND {} => {}
                SimpleEnumV2Shape::THIRD {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleEnumV2Shape {
        fn default() -> SimpleEnumV2Shape {
            SimpleEnumV2Shape::FIRST {}
        }
    }

    impl ::std::convert::AsRef<SimpleEnumV2Shape> for &SimpleEnumV2Shape {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleTypesEnumV2ClientCallHistory {}

    impl ISimpleTypesEnumV2ClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleTypesEnumV2Client {
        fn GetEnumV2(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumV2FirstKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumV2SecondKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumV2ThirdKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        Opaque {
            obj: ::dafny_runtime::Object<dyn::std::any::Any>,
        },
    }

    impl Error {
        pub fn list(
            &self,
        ) -> &::dafny_runtime::Sequence<
            ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
        > {
            match self {
                Error::CollectionOfErrors { list, message } => list,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn message(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                Error::CollectionOfErrors { list, message } => message,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
            match self {
                Error::CollectionOfErrors { list, message } => {
                    panic!("field does not exist on this variant")
                }
                Error::Opaque { obj } => obj,
            }
        }
    }

    impl ::std::fmt::Debug for Error {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for Error {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Error::CollectionOfErrors { list, message } => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.Error.CollectionOfErrors("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::Opaque { obj } => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_denumv2_dinternaldafny_dtypes.Error.Opaque("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(obj, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Error {}

    impl ::std::hash::Hash for Error {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Error::CollectionOfErrors { list, message } => {
                    list.hash(_state);
                    message.hash(_state)
                }
                Error::Opaque { obj } => obj.hash(_state),
            }
        }
    }

    impl ::std::default::Default for Error {
        fn default() -> Error {
            Error::CollectionOfErrors {
                list: ::std::default::Default::default(),
                message: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Error> for &Error {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type OpaqueError =
        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleEnumV2Impl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetEnumV2(
            config: &::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output> = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumV2FirstKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::FIRST {})) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output> = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::FIRST {})) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumV2SecondKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::SECOND {})) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output> = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::SECOND {})) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumV2ThirdKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::THIRD {})) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output> = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Shape::THIRD {})) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Config {
        Config {},
    }

    impl Config {}

    impl ::std::fmt::Debug for Config {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for Config {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Config::Config {} => {
                    write!(_formatter, "r#_SimpleEnumV2Impl_Compile.Config.Config")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Config {}

    impl ::std::hash::Hash for Config {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Config::Config {} => {}
            }
        }
    }

    impl ::std::default::Default for Config {
        fn default() -> Config {
            Config::Config {}
        }
    }

    impl ::std::convert::AsRef<Config> for &Config {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod r#_simple_dtypes_denumv2_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleEnumV2Config(
        ) -> ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Config>
        {
            ::std::rc::Rc::new(super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Config::SimpleEnumV2Config {})
        }
        pub fn SimpleEnumV2(
            config: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::SimpleEnumV2Config,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<
                super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client,
            > = super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client::_allocate_rcmut(
            );
            super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleEnumV2Impl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client>, ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client>, ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client>, ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client>, ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    pub struct SimpleEnumV2Client {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
    }

    impl SimpleEnumV2Client {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config>,
        ) -> () {
            let mut _set__i_config: bool = false;
            ::dafny_runtime::update_field_uninit_rcmut!(
                this.clone(),
                r#__i_config,
                _set__i_config,
                config.clone()
            );
            return ();
        }
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleEnumV2Impl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::ISimpleTypesEnumV2Client
        for super::r#_simple_dtypes_denumv2_dinternaldafny::SimpleEnumV2Client
    {
        fn GetEnumV2(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumV2Impl_Compile::_default::GetEnumV2(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetEnumV2FirstKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumV2Impl_Compile::_default::GetEnumV2FirstKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
        fn GetEnumV2SecondKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumV2Impl_Compile::_default::GetEnumV2SecondKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
        fn GetEnumV2ThirdKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Input,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
                        >,
                        ::std::rc::Rc<super::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumV2Impl_Compile::_default::GetEnumV2ThirdKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            return output.read();
        }
    }
}
pub mod _module {}
