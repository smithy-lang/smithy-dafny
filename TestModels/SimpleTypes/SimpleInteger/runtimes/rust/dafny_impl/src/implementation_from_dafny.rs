#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_dinteger_dinternaldafny_dtypes {
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
                    write!(_formatter, "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
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
    pub enum GetIntegerInput {
        GetIntegerInput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>>,
        },
    }

    impl GetIntegerInput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
            match self {
                GetIntegerInput::GetIntegerInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetIntegerInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetIntegerInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetIntegerInput::GetIntegerInput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.GetIntegerInput.GetIntegerInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetIntegerInput {}

    impl ::std::hash::Hash for GetIntegerInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetIntegerInput::GetIntegerInput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetIntegerInput {
        fn default() -> GetIntegerInput {
            GetIntegerInput::GetIntegerInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetIntegerInput> for &GetIntegerInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetIntegerOutput {
        GetIntegerOutput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>>,
        },
    }

    impl GetIntegerOutput {
        pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
            match self {
                GetIntegerOutput::GetIntegerOutput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetIntegerOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetIntegerOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetIntegerOutput::GetIntegerOutput { value } => {
                    write!(_formatter, "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.GetIntegerOutput.GetIntegerOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetIntegerOutput {}

    impl ::std::hash::Hash for GetIntegerOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetIntegerOutput::GetIntegerOutput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetIntegerOutput {
        fn default() -> GetIntegerOutput {
            GetIntegerOutput::GetIntegerOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetIntegerOutput> for &GetIntegerOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleIntegerConfig {
        SimpleIntegerConfig {},
    }

    impl SimpleIntegerConfig {}

    impl ::std::fmt::Debug for SimpleIntegerConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleIntegerConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleIntegerConfig::SimpleIntegerConfig {} => {
                    write!(_formatter, "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.SimpleIntegerConfig.SimpleIntegerConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleIntegerConfig {}

    impl ::std::hash::Hash for SimpleIntegerConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleIntegerConfig::SimpleIntegerConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleIntegerConfig {
        fn default() -> SimpleIntegerConfig {
            SimpleIntegerConfig::SimpleIntegerConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleIntegerConfig> for &SimpleIntegerConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleTypesIntegerClientCallHistory {}

    impl ISimpleTypesIntegerClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleTypesIntegerClient {
        fn GetInteger(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetIntegerKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
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
                        "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_dtypes_dinteger_dinternaldafny_dtypes.Error.Opaque("
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
        ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleIntegerImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetInteger(
            config: &::std::rc::Rc<super::r#_SimpleIntegerImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetIntegerKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleIntegerImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
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
                    write!(_formatter, "r#_SimpleIntegerImpl_Compile.Config.Config")?;
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
pub mod r#_simple_dtypes_dinteger_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleIntegerConfig() -> ::std::rc::Rc<
            super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::SimpleIntegerConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::SimpleIntegerConfig::SimpleIntegerConfig {})
        }
        pub fn SimpleInteger(
            config: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::SimpleIntegerConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                        >,
                        ::std::rc::Rc<
                            super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient> = super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient::_allocate_rcmut();
            super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleIntegerImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    pub struct SimpleIntegerClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleIntegerImpl_Compile::Config>,
    }

    impl SimpleIntegerClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleIntegerImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleIntegerImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::ISimpleTypesIntegerClient
        for super::r#_simple_dtypes_dinteger_dinternaldafny::SimpleIntegerClient
    {
        fn GetInteger(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleIntegerImpl_Compile::_default::GetInteger(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetIntegerKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleIntegerImpl_Compile::_default::GetIntegerKnownValueTest(
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