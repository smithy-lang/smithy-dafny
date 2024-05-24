#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;
    
pub mod r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes {
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
                    write!(_formatter, "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
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
    pub enum GetDoubleInput {
        GetDoubleInput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<f64>>,
        },
    }

    impl GetDoubleInput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<f64>> {
            match self {
                GetDoubleInput::GetDoubleInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetDoubleInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetDoubleInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetDoubleInput::GetDoubleInput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.GetDoubleInput.GetDoubleInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetDoubleInput {}
/*
    impl ::std::hash::Hash for GetDoubleInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetDoubleInput::GetDoubleInput { value } => value.hash(_state),
            }
        }
    }
*/
    impl ::std::default::Default for GetDoubleInput {
        fn default() -> GetDoubleInput {
            GetDoubleInput::GetDoubleInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetDoubleInput> for &GetDoubleInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetDoubleOutput {
        GetDoubleOutput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<f64>>,
        },
    }

    impl GetDoubleOutput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<f64>> {
            match self {
                GetDoubleOutput::GetDoubleOutput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetDoubleOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetDoubleOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetDoubleOutput::GetDoubleOutput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.GetDoubleOutput.GetDoubleOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetDoubleOutput {}
/*
    impl ::std::hash::Hash for GetDoubleOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetDoubleOutput::GetDoubleOutput { value } => value.hash(_state),
            }
        }
    }
*/
    impl ::std::default::Default for GetDoubleOutput {
        fn default() -> GetDoubleOutput {
            GetDoubleOutput::GetDoubleOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetDoubleOutput> for &GetDoubleOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleDoubleConfig {
        SimpleDoubleConfig {},
    }

    impl SimpleDoubleConfig {}

    impl ::std::fmt::Debug for SimpleDoubleConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleDoubleConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleDoubleConfig::SimpleDoubleConfig {} => {
                    write!(_formatter, "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.SimpleDoubleConfig.SimpleDoubleConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleDoubleConfig {}

    impl ::std::hash::Hash for SimpleDoubleConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleDoubleConfig::SimpleDoubleConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleDoubleConfig {
        fn default() -> SimpleDoubleConfig {
            SimpleDoubleConfig::SimpleDoubleConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleDoubleConfig> for &SimpleDoubleConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleTypesDoubleClientCallHistory {}

    impl ISimpleTypesDoubleClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleTypesDoubleClient {
        fn GetDouble(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetDoubleKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
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
                    write!(_formatter, "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.Error.CollectionOfErrors(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::Opaque { obj } => {
                    write!(
                        _formatter,
                        "r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes.Error.Opaque("
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
        ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleDoubleImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetDouble(
            config: &::std::rc::Rc<super::r#_SimpleDoubleImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            super::r#_SimpleDoubleImpl_Compile::_default::ValidateDoubleType(*input.value().value());
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput::GetDoubleOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput::GetDoubleOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            super::r#_SimpleDoubleImpl_Compile::_default::ValidateDoubleType(*res.value().value());
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetDoubleKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleDoubleImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            super::r#_SimpleDoubleImpl_Compile::_default::ValidateDoubleType(*input.value().value());
            if !(input.value().value() == &33f64) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput::GetDoubleOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput::GetDoubleOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            super::r#_SimpleDoubleImpl_Compile::_default::ValidateDoubleType(*res.value().value());
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn ValidateDoubleType(input: f64) -> () {
	    return;

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
                    write!(_formatter, "r#_SimpleDoubleImpl_Compile.Config.Config")?;
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
pub mod r#_simple_dtypes_ddouble_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleDoubleConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::SimpleDoubleConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::SimpleDoubleConfig::SimpleDoubleConfig {})
        }
        pub fn SimpleDouble(
            config: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::SimpleDoubleConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient> = super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient::_allocate_rcmut();
            super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleDoubleImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    pub struct SimpleDoubleClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleDoubleImpl_Compile::Config>,
    }

    impl SimpleDoubleClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleDoubleImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleDoubleImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::ISimpleTypesDoubleClient
        for super::r#_simple_dtypes_ddouble_dinternaldafny::SimpleDoubleClient
    {
        fn GetDouble(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleDoubleImpl_Compile::_default::GetDouble(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetDoubleKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleDoubleImpl_Compile::_default::GetDoubleKnownValueTest(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
    }
}
pub mod _module {}
