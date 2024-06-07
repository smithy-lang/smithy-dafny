#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_derrors_dinternaldafny_dtypes {
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
                    write!(
                        _formatter,
                        "r#_simple_derrors_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent("
                    )?;
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
    pub enum GetErrorsInput {
        GetErrorsInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetErrorsInput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetErrorsInput::GetErrorsInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetErrorsInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetErrorsInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetErrorsInput::GetErrorsInput { value } => {
                    write!(
                        _formatter,
                        "r#_simple_derrors_dinternaldafny_dtypes.GetErrorsInput.GetErrorsInput("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetErrorsInput {}

    impl ::std::hash::Hash for GetErrorsInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetErrorsInput::GetErrorsInput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetErrorsInput {
        fn default() -> GetErrorsInput {
            GetErrorsInput::GetErrorsInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetErrorsInput> for &GetErrorsInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetErrorsOutput {
        GetErrorsOutput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetErrorsOutput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetErrorsOutput::GetErrorsOutput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetErrorsOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetErrorsOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetErrorsOutput::GetErrorsOutput { value } => {
                    write!(
                        _formatter,
                        "r#_simple_derrors_dinternaldafny_dtypes.GetErrorsOutput.GetErrorsOutput("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetErrorsOutput {}

    impl ::std::hash::Hash for GetErrorsOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetErrorsOutput::GetErrorsOutput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetErrorsOutput {
        fn default() -> GetErrorsOutput {
            GetErrorsOutput::GetErrorsOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetErrorsOutput> for &GetErrorsOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleErrorsClientCallHistory {}

    impl ISimpleErrorsClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleErrorsClient {
        fn AlwaysError(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn AlwaysMultipleErrors(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn AlwaysNativeError(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleErrorsConfig {
        SimpleErrorsConfig {},
    }

    impl SimpleErrorsConfig {}

    impl ::std::fmt::Debug for SimpleErrorsConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleErrorsConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleErrorsConfig::SimpleErrorsConfig {} => {
                    write!(_formatter, "r#_simple_derrors_dinternaldafny_dtypes.SimpleErrorsConfig.SimpleErrorsConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleErrorsConfig {}

    impl ::std::hash::Hash for SimpleErrorsConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleErrorsConfig::SimpleErrorsConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleErrorsConfig {
        fn default() -> SimpleErrorsConfig {
            SimpleErrorsConfig::SimpleErrorsConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleErrorsConfig> for &SimpleErrorsConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        SimpleErrorsException {
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        Opaque {
            obj: ::dafny_runtime::Object<dyn::std::any::Any>,
        },
    }

    impl Error {
        pub fn message(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                Error::SimpleErrorsException { message } => message,
                Error::CollectionOfErrors { list, message } => message,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn list(
            &self,
        ) -> &::dafny_runtime::Sequence<
            ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
        > {
            match self {
                Error::SimpleErrorsException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::CollectionOfErrors { list, message } => list,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
            match self {
                Error::SimpleErrorsException { message } => {
                    panic!("field does not exist on this variant")
                }
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
                Error::SimpleErrorsException { message } => {
                    write!(
                        _formatter,
                        "r#_simple_derrors_dinternaldafny_dtypes.Error.SimpleErrorsException("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::CollectionOfErrors { list, message } => {
                    write!(
                        _formatter,
                        "r#_simple_derrors_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_derrors_dinternaldafny_dtypes.Error.Opaque("
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
                Error::SimpleErrorsException { message } => message.hash(_state),
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
            Error::SimpleErrorsException {
                message: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Error> for &Error {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type OpaqueError = ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleErrorsImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn AlwaysError(
            config: &::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config>,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error> =
                ::std::rc::Rc::new(
                    super::r#_simple_derrors_dinternaldafny_dtypes::Error::SimpleErrorsException {
                        message: input.value().value().clone(),
                    },
                );
            res = ::std::rc::Rc::new(
                super::r#_simple_derrors_dinternaldafny_dtypes::Error::SimpleErrorsException {
                    message: input.value().value().clone(),
                },
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                >::Failure {
                    error: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn AlwaysMultipleErrors(
            config: &::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config>,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error> = ::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::CollectionOfErrors {
            list: ::dafny_runtime::seq![::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::SimpleErrorsException {
                    message: input.value().value().clone()
                  })],
            message: ::dafny_runtime::string_utf16_of("Something")
          });
            res = ::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::CollectionOfErrors {
            list: ::dafny_runtime::seq![::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::SimpleErrorsException {
                    message: input.value().value().clone()
                  })],
            message: ::dafny_runtime::string_utf16_of("Something")
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                >::Failure {
                    error: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn AlwaysNativeError(
            config: &::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config>,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut opaqueObject = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_SimpleErrorsImpl_Compile::SomeOpaqueGeneratedTypeForTesting,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_SimpleErrorsImpl_Compile::SomeOpaqueGeneratedTypeForTesting> = super::r#_SimpleErrorsImpl_Compile::SomeOpaqueGeneratedTypeForTesting::_allocate_rcmut();
            super::r#_SimpleErrorsImpl_Compile::SomeOpaqueGeneratedTypeForTesting::_ctor(&_nw0);
            opaqueObject = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            let mut res: ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error> = ::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::Opaque {
            obj: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn ::std::any::Any>>::upcast_to(opaqueObject.read())
          });
            res = ::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::Error::Opaque {
            obj: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn ::std::any::Any>>::upcast_to(opaqueObject.read())
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                >::Failure {
                    error: res.clone(),
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
                    write!(_formatter, "r#_SimpleErrorsImpl_Compile.Config.Config")?;
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

    pub struct SomeOpaqueGeneratedTypeForTesting {}

    impl SomeOpaqueGeneratedTypeForTesting {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(this: &::dafny_runtime::Object<Self>) -> () {
            return ();
        }
    }
}
pub mod r#_simple_derrors_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleErrorsConfig(
        ) -> ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::SimpleErrorsConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_derrors_dinternaldafny_dtypes::SimpleErrorsConfig::SimpleErrorsConfig {})
        }
        pub fn SimpleErrors(
            config: &::std::rc::Rc<
                super::r#_simple_derrors_dinternaldafny_dtypes::SimpleErrorsConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient,
                >,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient,
                >,
            >::new();
            let mut _nw1: ::dafny_runtime::Object<
                super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient,
            > = super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient::_allocate_rcmut();
            super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient::_ctor(
                &_nw1,
                &::std::rc::Rc::new(super::r#_SimpleErrorsImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw1.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient,
                >,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient,
                >,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >::Success {
                value: client.clone(),
            })
        }
        pub fn CreateFailureOfError(
            error: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient,
                >,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient,
                >,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >::Failure {
                error: error.clone(),
            })
        }
    }

    pub struct SimpleErrorsClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config>,
    }

    impl SimpleErrorsClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleErrorsImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_derrors_dinternaldafny_dtypes::ISimpleErrorsClient
        for super::r#_simple_derrors_dinternaldafny::SimpleErrorsClient
    {
        fn AlwaysError(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleErrorsImpl_Compile::_default::AlwaysError(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn AlwaysMultipleErrors(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleErrorsImpl_Compile::_default::AlwaysMultipleErrors(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
        fn AlwaysNativeError(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput>,
                ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_derrors_dinternaldafny_dtypes::GetErrorsOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_derrors_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleErrorsImpl_Compile::_default::AlwaysNativeError(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
    }
}
pub mod _module {}
