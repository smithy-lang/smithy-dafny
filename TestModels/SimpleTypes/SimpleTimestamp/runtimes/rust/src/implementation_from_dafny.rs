#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod timestamp {
            pub mod internaldafny {
                pub use crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleTimestampConfig() -> ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::SimpleTimestampConfig>{
                        ::std::rc::Rc::new(crate::simple::types::timestamp::internaldafny::types::SimpleTimestampConfig::SimpleTimestampConfig {})
                    }
                    pub fn SimpleTimestamp(config: &::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::SimpleTimestampConfig>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::timestamp::internaldafny::SimpleTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>{
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::timestamp::internaldafny::SimpleTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<crate::simple::types::timestamp::internaldafny::SimpleTimestampClient>>::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::timestamp::internaldafny::SimpleTimestampClient> = crate::simple::types::timestamp::internaldafny::SimpleTimestampClient::_allocate_object();
                        crate::simple::types::timestamp::internaldafny::SimpleTimestampClient::_ctor(&_nw0, &::std::rc::Rc::new(crate::r#_SimpleTypesTimestampImpl_Compile::Config::Config {}));
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::timestamp::internaldafny::SimpleTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleTimestampClient {
                    pub r#__i_config:
                        ::std::rc::Rc<crate::r#_SimpleTypesTimestampImpl_Compile::Config>,
                }

                impl SimpleTimestampClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::timestamp::internaldafny::SimpleTimestampClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleTypesTimestampImpl_Compile::Config>,
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
                    pub fn config(
                        &self,
                    ) -> ::std::rc::Rc<crate::r#_SimpleTypesTimestampImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any>
                    for crate::simple::types::timestamp::internaldafny::SimpleTimestampClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesTimestampClient
                    for crate::simple::types::timestamp::internaldafny::SimpleTimestampClient
                {
                    fn GetTimestamp(&mut self, input: &::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleTypesTimestampImpl_Compile::_default::GetTimestamp(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesTimestampClient>
                    for crate::simple::types::timestamp::internaldafny::SimpleTimestampClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClient);
                }

                pub mod types {
                    pub use dafny_runtime::DafnyPrint;
                    pub use dafny_runtime::UpcastObject;
                    pub use std::any::Any;
                    pub use std::cmp::Eq;
                    pub use std::convert::AsRef;
                    pub use std::default::Default;
                    pub use std::fmt::Debug;
                    pub use std::hash::Hash;

                    #[derive(PartialEq, Clone)]
                    pub enum DafnyCallEvent<
                        I: ::dafny_runtime::DafnyType,
                        O: ::dafny_runtime::DafnyType,
                    > {
                        DafnyCallEvent { input: I, output: O },
                    }

                    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> DafnyCallEvent<I, O> {
                        pub fn input(&self) -> &I {
                            match self {
                                DafnyCallEvent::DafnyCallEvent { input, output } => input,
                            }
                        }
                        pub fn output(&self) -> &O {
                            match self {
                                DafnyCallEvent::DafnyCallEvent { input, output } => output,
                            }
                        }
                    }

                    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> Debug for DafnyCallEvent<I, O> {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> DafnyPrint
                        for DafnyCallEvent<I, O>
                    {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                DafnyCallEvent::DafnyCallEvent { input, output } => {
                                    write!(_formatter, "simple.types.timestamp.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        input, _formatter, false,
                                    )?;
                                    write!(_formatter, ", ")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        output, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl<
                            I: ::dafny_runtime::DafnyType + Eq,
                            O: ::dafny_runtime::DafnyType + Eq,
                        > Eq for DafnyCallEvent<I, O>
                    {
                    }

                    impl<
                            I: ::dafny_runtime::DafnyType + Hash,
                            O: ::dafny_runtime::DafnyType + Hash,
                        > Hash for DafnyCallEvent<I, O>
                    {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                DafnyCallEvent::DafnyCallEvent { input, output } => {
                                    ::std::hash::Hash::hash(input, _state);
                                    ::std::hash::Hash::hash(output, _state)
                                }
                            }
                        }
                    }

                    impl<
                            I: ::dafny_runtime::DafnyType + Default,
                            O: ::dafny_runtime::DafnyType + Default,
                        > Default for DafnyCallEvent<I, O>
                    {
                        fn default() -> DafnyCallEvent<I, O> {
                            DafnyCallEvent::DafnyCallEvent {
                                input: ::std::default::Default::default(),
                                output: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType>
                        AsRef<DafnyCallEvent<I, O>> for &DafnyCallEvent<I, O>
                    {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetTimestampInput {
                        GetTimestampInput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<
                                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                >,
                            >,
                        },
                    }

                    impl GetTimestampInput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        > {
                            match self {
                                GetTimestampInput::GetTimestampInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetTimestampInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetTimestampInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetTimestampInput::GetTimestampInput { value } => {
                                    write!(_formatter, "simple.types.timestamp.internaldafny.types.GetTimestampInput.GetTimestampInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetTimestampInput {}

                    impl Hash for GetTimestampInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetTimestampInput::GetTimestampInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetTimestampInput {
                        fn default() -> GetTimestampInput {
                            GetTimestampInput::GetTimestampInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetTimestampInput> for &GetTimestampInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetTimestampOutput {
                        GetTimestampOutput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<
                                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                >,
                            >,
                        },
                    }

                    impl GetTimestampOutput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        > {
                            match self {
                                GetTimestampOutput::GetTimestampOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetTimestampOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetTimestampOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetTimestampOutput::GetTimestampOutput { value } => {
                                    write!(_formatter, "simple.types.timestamp.internaldafny.types.GetTimestampOutput.GetTimestampOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetTimestampOutput {}

                    impl Hash for GetTimestampOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetTimestampOutput::GetTimestampOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetTimestampOutput {
                        fn default() -> GetTimestampOutput {
                            GetTimestampOutput::GetTimestampOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetTimestampOutput> for &GetTimestampOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleTimestampConfig {
                        SimpleTimestampConfig {},
                    }

                    impl SimpleTimestampConfig {}

                    impl Debug for SimpleTimestampConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleTimestampConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleTimestampConfig::SimpleTimestampConfig {} => {
                                    write!(_formatter, "simple.types.timestamp.internaldafny.types.SimpleTimestampConfig.SimpleTimestampConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleTimestampConfig {}

                    impl Hash for SimpleTimestampConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleTimestampConfig::SimpleTimestampConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleTimestampConfig {
                        fn default() -> SimpleTimestampConfig {
                            SimpleTimestampConfig::SimpleTimestampConfig {}
                        }
                    }

                    impl AsRef<SimpleTimestampConfig> for &SimpleTimestampConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesTimestampClientCallHistory {}

                    impl ISimpleTypesTimestampClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::timestamp::internaldafny::types::ISimpleTypesTimestampClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesTimestampClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetTimestamp(&mut self, input: &::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::timestamp::internaldafny::types::Error,
                                >,
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
                            ::std::rc::Rc<
                                crate::simple::types::timestamp::internaldafny::types::Error,
                            >,
                        > {
                            match self {
                                Error::CollectionOfErrors { list, message } => list,
                                Error::Opaque { obj } => {
                                    panic!("field does not exist on this variant")
                                }
                            }
                        }
                        pub fn message(
                            &self,
                        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                        {
                            match self {
                                Error::CollectionOfErrors { list, message } => message,
                                Error::Opaque { obj } => {
                                    panic!("field does not exist on this variant")
                                }
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

                    impl Debug for Error {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for Error {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                Error::CollectionOfErrors { list, message } => {
                                    write!(_formatter, "simple.types.timestamp.internaldafny.types.Error.CollectionOfErrors(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        list, _formatter, false,
                                    )?;
                                    write!(_formatter, ", ")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        message, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                                Error::Opaque { obj } => {
                                    write!(
                                        _formatter,
                                        "simple.types.timestamp.internaldafny.types.Error.Opaque("
                                    )?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(obj, _formatter, false)?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for Error {}

                    impl Hash for Error {
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

                    impl Default for Error {
                        fn default() -> Error {
                            Error::CollectionOfErrors {
                                list: ::std::default::Default::default(),
                                message: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<Error> for &Error {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub type OpaqueError =
                        ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>;
                }
            }
        }
    }
}
pub mod r#_SimpleTypesTimestampImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetTimestamp(
            config: &::std::rc::Rc<crate::r#_SimpleTypesTimestampImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::timestamp::internaldafny::types::GetTimestampInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput,
                >,
                ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput>, ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>>>>::new();
            let mut res: ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput> = ::std::rc::Rc::new(crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput::GetTimestampOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::timestamp::internaldafny::types::GetTimestampOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::timestamp::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Config {
        Config {},
    }

    impl Config {}

    impl Debug for Config {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl DafnyPrint for Config {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Config::Config {} => {
                    write!(_formatter, "SimpleTypesTimestampImpl_Compile.Config.Config")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Config {}

    impl Hash for Config {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Config::Config {} => {}
            }
        }
    }

    impl Default for Config {
        fn default() -> Config {
            Config::Config {}
        }
    }

    impl AsRef<Config> for &Config {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod _module {}
