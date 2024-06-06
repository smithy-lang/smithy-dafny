#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes {
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
                    write!(_formatter, "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
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
    pub enum GetEnumInput {
        GetEnumInput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape>>,
        },
    }

    impl GetEnumInput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape>> {
            match self {
                GetEnumInput::GetEnumInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetEnumInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetEnumInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetEnumInput::GetEnumInput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.GetEnumInput.GetEnumInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetEnumInput {}

    impl ::std::hash::Hash for GetEnumInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetEnumInput::GetEnumInput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetEnumInput {
        fn default() -> GetEnumInput {
            GetEnumInput::GetEnumInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetEnumInput> for &GetEnumInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetEnumOutput {
        GetEnumOutput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape>>,
        },
    }

    impl GetEnumOutput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape>> {
            match self {
                GetEnumOutput::GetEnumOutput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetEnumOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetEnumOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetEnumOutput::GetEnumOutput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.GetEnumOutput.GetEnumOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetEnumOutput {}

    impl ::std::hash::Hash for GetEnumOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetEnumOutput::GetEnumOutput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetEnumOutput {
        fn default() -> GetEnumOutput {
            GetEnumOutput::GetEnumOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetEnumOutput> for &GetEnumOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleEnumConfig {
        SimpleEnumConfig {},
    }

    impl SimpleEnumConfig {}

    impl ::std::fmt::Debug for SimpleEnumConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleEnumConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleEnumConfig::SimpleEnumConfig {} => {
                    write!(_formatter, "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.SimpleEnumConfig.SimpleEnumConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleEnumConfig {}

    impl ::std::hash::Hash for SimpleEnumConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleEnumConfig::SimpleEnumConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleEnumConfig {
        fn default() -> SimpleEnumConfig {
            SimpleEnumConfig::SimpleEnumConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleEnumConfig> for &SimpleEnumConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleEnumShape {
        FIRST,
        SECOND,
        THIRD,
    }

    impl SimpleEnumShape {}

    impl ::std::fmt::Debug for SimpleEnumShape {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleEnumShape {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleEnumShape::FIRST {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.SimpleEnumShape.FIRST"
                    )?;
                    Ok(())
                }
                SimpleEnumShape::SECOND {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.SimpleEnumShape.SECOND"
                    )?;
                    Ok(())
                }
                SimpleEnumShape::THIRD {} => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.SimpleEnumShape.THIRD"
                    )?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleEnumShape {}

    impl ::std::hash::Hash for SimpleEnumShape {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleEnumShape::FIRST {} => {}
                SimpleEnumShape::SECOND {} => {}
                SimpleEnumShape::THIRD {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleEnumShape {
        fn default() -> SimpleEnumShape {
            SimpleEnumShape::FIRST {}
        }
    }

    impl ::std::convert::AsRef<SimpleEnumShape> for &SimpleEnumShape {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleTypesEnumClientCallHistory {}

    impl ISimpleTypesEnumClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleTypesEnumClient {
        fn GetEnum(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumFirstKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumSecondKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetEnumThirdKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
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
                    write!(_formatter, "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.Error.CollectionOfErrors(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::Opaque { obj } => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes.Error.Opaque("
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
        ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleEnumImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetEnum(
            config: &::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumFirstKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::FIRST) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::FIRST) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumSecondKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::SECOND) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::SECOND) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetEnumThirdKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(input.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::THIRD) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(res.value().value().clone() == super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumShape::THIRD) {
        panic!("Halt")
      };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
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
                    write!(_formatter, "r#_SimpleEnumImpl_Compile.Config.Config")?;
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
pub mod r#_simple_dtypes_dsmithyenum_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleEnumConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumConfig::SimpleEnumConfig {})
        }
        pub fn SimpleEnum(
            config: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::SimpleEnumConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient> = super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient::_allocate_rcmut();
            super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleEnumImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    pub struct SimpleEnumClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
    }

    impl SimpleEnumClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleEnumImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::ISimpleTypesEnumClient
        for super::r#_simple_dtypes_dsmithyenum_dinternaldafny::SimpleEnumClient
    {
        fn GetEnum(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumImpl_Compile::_default::GetEnum(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetEnumFirstKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumImpl_Compile::_default::GetEnumFirstKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
        fn GetEnumSecondKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumImpl_Compile::_default::GetEnumSecondKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
        fn GetEnumThirdKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleEnumImpl_Compile::_default::GetEnumThirdKnownValueTest(
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
