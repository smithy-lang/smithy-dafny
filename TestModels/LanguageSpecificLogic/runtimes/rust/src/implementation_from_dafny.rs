#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_language_dspecific_dlogic_dinternaldafny_dtypes {
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
                    write!(_formatter, "language.specific.logic.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    ::std::hash::Hash::hash(input, _state);
                    ::std::hash::Hash::hash(output, _state)
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
    pub enum GetRuntimeInformationOutput {
        GetRuntimeInformationOutput {
            language: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            runtime: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
    }

    impl GetRuntimeInformationOutput {
        pub fn language(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                GetRuntimeInformationOutput::GetRuntimeInformationOutput { language, runtime } => {
                    language
                }
            }
        }
        pub fn runtime(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                GetRuntimeInformationOutput::GetRuntimeInformationOutput { language, runtime } => {
                    runtime
                }
            }
        }
    }

    impl ::std::fmt::Debug for GetRuntimeInformationOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetRuntimeInformationOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetRuntimeInformationOutput::GetRuntimeInformationOutput { language, runtime } => {
                    write!(_formatter, "language.specific.logic.internaldafny.types.GetRuntimeInformationOutput.GetRuntimeInformationOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(language, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(runtime, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetRuntimeInformationOutput {}

    impl ::std::hash::Hash for GetRuntimeInformationOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetRuntimeInformationOutput::GetRuntimeInformationOutput { language, runtime } => {
                    ::std::hash::Hash::hash(language, _state);
                    ::std::hash::Hash::hash(runtime, _state)
                }
            }
        }
    }

    impl ::std::default::Default for GetRuntimeInformationOutput {
        fn default() -> GetRuntimeInformationOutput {
            GetRuntimeInformationOutput::GetRuntimeInformationOutput {
                language: ::std::default::Default::default(),
                runtime: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetRuntimeInformationOutput> for &GetRuntimeInformationOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ILanguageSpecificLogicClientCallHistory {}

    impl ILanguageSpecificLogicClientCallHistory {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any>
    for super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClientCallHistory {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
  }

    pub trait ILanguageSpecificLogicClient:
        ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
    {
        fn GetRuntimeInformation(&mut self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>;
    }

    #[derive(PartialEq, Clone)]
    pub enum LanguageSpecificLogicConfig {
        LanguageSpecificLogicConfig {},
    }

    impl LanguageSpecificLogicConfig {}

    impl ::std::fmt::Debug for LanguageSpecificLogicConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for LanguageSpecificLogicConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                LanguageSpecificLogicConfig::LanguageSpecificLogicConfig {} => {
                    write!(_formatter, "language.specific.logic.internaldafny.types.LanguageSpecificLogicConfig.LanguageSpecificLogicConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for LanguageSpecificLogicConfig {}

    impl ::std::hash::Hash for LanguageSpecificLogicConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                LanguageSpecificLogicConfig::LanguageSpecificLogicConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for LanguageSpecificLogicConfig {
        fn default() -> LanguageSpecificLogicConfig {
            LanguageSpecificLogicConfig::LanguageSpecificLogicConfig {}
        }
    }

    impl ::std::convert::AsRef<LanguageSpecificLogicConfig> for &LanguageSpecificLogicConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>,
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
                        "language.specific.logic.internaldafny.types.Error.CollectionOfErrors("
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
                        "language.specific.logic.internaldafny.types.Error.Opaque("
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
                    ::std::hash::Hash::hash(list, _state);
                    ::std::hash::Hash::hash(message, _state)
                }
                Error::Opaque { obj } => ::std::hash::Hash::hash(obj, _state),
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
        ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>;
}
pub mod r#_LanguageSpecificLogicImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetRuntimeInformation(config: &::std::rc::Rc<super::r#_LanguageSpecificLogicImpl_Compile::Config>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::std::rc::Rc<
                            super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::std::rc::Rc<
                            super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error,
                        >,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_LanguageSpecificLogicImpl_Compile::_default::GetRustRuntimeVersion(
                    config,
                ),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut runtimeInfo: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError0.read().Extract();
            let mut getRuntimeInformationOutput: ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput> = ::std::rc::Rc::new(super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput::GetRuntimeInformationOutput {
            language: ::dafny_runtime::string_utf16_of("Rust"),
            runtime: runtimeInfo.clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>::Success {
              value: getRuntimeInformationOutput.clone()
            }));
            return output.read();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_LanguageSpecificLogicImpl_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
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
                    write!(
                        _formatter,
                        "LanguageSpecificLogicImpl_Compile.Config.Config"
                    )?;
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
pub mod r#_language_dspecific_dlogic_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn DefaultLanguageSpecificLogicConfig() -> ::std::rc::Rc<
            super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::LanguageSpecificLogicConfig,
        > {
            ::std::rc::Rc::new(super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::LanguageSpecificLogicConfig::LanguageSpecificLogicConfig {})
        }
        pub fn LanguageSpecificLogic(
            config: &::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::LanguageSpecificLogicConfig>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient,
                >,
                ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient> = super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient::_allocate_object();
            super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_LanguageSpecificLogicImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>::Success {
              value: client.read()
            }));
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_language_dspecific_dlogic_dinternaldafny::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    pub struct LanguageSpecificLogicClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_LanguageSpecificLogicImpl_Compile::Config>,
    }

    impl LanguageSpecificLogicClient {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<
                super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient,
            >,
            config: &::std::rc::Rc<super::r#_LanguageSpecificLogicImpl_Compile::Config>,
        ) -> () {
            let mut _set__i_config: bool = false;
            ::dafny_runtime::update_field_uninit_object!(
                this.clone(),
                r#__i_config,
                _set__i_config,
                config.clone()
            );
            return ();
        }
        pub fn config(&self) -> ::std::rc::Rc<super::r#_LanguageSpecificLogicImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    impl super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient
        for super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient
    {
        fn GetRuntimeInformation(&mut self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::GetRuntimeInformationOutput>, ::std::rc::Rc<super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_LanguageSpecificLogicImpl_Compile::_default::GetRuntimeInformation(
                    &self.config().clone(),
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient>
    for super::r#_language_dspecific_dlogic_dinternaldafny::LanguageSpecificLogicClient {
    ::dafny_runtime::UpcastObjectFn!(dyn super::r#_language_dspecific_dlogic_dinternaldafny_dtypes::ILanguageSpecificLogicClient);
  }
}
pub mod _module {}
