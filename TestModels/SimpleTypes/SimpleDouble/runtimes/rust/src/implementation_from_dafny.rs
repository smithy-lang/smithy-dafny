#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod smithydouble {
            pub mod internaldafny {
                pub use crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleDoubleConfig() -> ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::SimpleDoubleConfig>{
                        ::std::rc::Rc::new(crate::simple::types::smithydouble::internaldafny::types::SimpleDoubleConfig::SimpleDoubleConfig {})
                    }
                    pub fn SimpleDouble(config: &::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::SimpleDoubleConfig>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>{
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient>>::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient> = crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient::_allocate_object();
                        crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient::_ctor(&_nw0, &::std::rc::Rc::new(crate::r#_SimpleSmithyDoubleOperations_Compile::Config::Config {}));
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleDoubleClient {
                    pub r#__i_config:
                        ::std::rc::Rc<crate::r#_SimpleSmithyDoubleOperations_Compile::Config>,
                }

                impl SimpleDoubleClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient,
                        >,
                        config: &::std::rc::Rc<
                            crate::r#_SimpleSmithyDoubleOperations_Compile::Config,
                        >,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleSmithyDoubleOperations_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any>
                    for crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesDoubleClient
                    for crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient
                {
                    fn GetDouble(&mut self, input: &::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleSmithyDoubleOperations_Compile::_default::GetDouble(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesDoubleClient>
                    for crate::simple::types::smithydouble::internaldafny::SimpleDoubleClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClient);
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
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetDoubleInput {
                        GetDoubleInput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                            >,
                        },
                    }

                    impl GetDoubleInput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        > {
                            match self {
                                GetDoubleInput::GetDoubleInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetDoubleInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetDoubleInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetDoubleInput::GetDoubleInput { value } => {
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.GetDoubleInput.GetDoubleInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetDoubleInput {}

                    impl Hash for GetDoubleInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetDoubleInput::GetDoubleInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetDoubleInput {
                        fn default() -> GetDoubleInput {
                            GetDoubleInput::GetDoubleInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetDoubleInput> for &GetDoubleInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetDoubleOutput {
                        GetDoubleOutput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                            >,
                        },
                    }

                    impl GetDoubleOutput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        > {
                            match self {
                                GetDoubleOutput::GetDoubleOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetDoubleOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetDoubleOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetDoubleOutput::GetDoubleOutput { value } => {
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.GetDoubleOutput.GetDoubleOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetDoubleOutput {}

                    impl Hash for GetDoubleOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetDoubleOutput::GetDoubleOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetDoubleOutput {
                        fn default() -> GetDoubleOutput {
                            GetDoubleOutput::GetDoubleOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetDoubleOutput> for &GetDoubleOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleDoubleConfig {
                        SimpleDoubleConfig {},
                    }

                    impl SimpleDoubleConfig {}

                    impl Debug for SimpleDoubleConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleDoubleConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleDoubleConfig::SimpleDoubleConfig {} => {
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.SimpleDoubleConfig.SimpleDoubleConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleDoubleConfig {}

                    impl Hash for SimpleDoubleConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleDoubleConfig::SimpleDoubleConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleDoubleConfig {
                        fn default() -> SimpleDoubleConfig {
                            SimpleDoubleConfig::SimpleDoubleConfig {}
                        }
                    }

                    impl AsRef<SimpleDoubleConfig> for &SimpleDoubleConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesDoubleClientCallHistory {}

                    impl ISimpleTypesDoubleClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::smithydouble::internaldafny::types::ISimpleTypesDoubleClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesDoubleClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetDouble(&mut self, input: &::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::smithydouble::internaldafny::types::Error,
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
                                crate::simple::types::smithydouble::internaldafny::types::Error,
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
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                    write!(_formatter, "simple.types.smithydouble.internaldafny.types.Error.Opaque(")?;
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

                    pub type OpaqueError = ::std::rc::Rc<
                        crate::simple::types::smithydouble::internaldafny::types::Error,
                    >;
                }
            }
        }
    }
}
pub mod r#_SimpleSmithyDoubleOperations_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn r#_ValidInternalConfig_q(
            config: &::std::rc::Rc<crate::r#_SimpleSmithyDoubleOperations_Compile::Config>,
        ) -> bool {
            true
        }
        pub fn GetDouble(
            config: &::std::rc::Rc<crate::r#_SimpleSmithyDoubleOperations_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithydouble::internaldafny::types::GetDoubleInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput>, ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>>>>::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut check: bool = <bool as std::default::Default>::default();
            let mut _out0: bool = <bool as std::default::Default>::default();
            _out0 = crate::r#_SimpleSmithyDoubleOperations_Compile::_default::ValidateDoubleType(
                input.value().value(),
            );
            check = _out0;
            if !check {
                panic!("Halt")
            };
            let mut result: ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput> = ::std::rc::Rc::new(crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput::GetDoubleOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithydouble::internaldafny::types::GetDoubleOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithydouble::internaldafny::types::Error>,
                >::Success {
                    value: result.clone(),
                },
            ));
            return output.read();
        }
        pub fn ValidateDoubleType(input: &::dafny_runtime::Sequence<u8>) -> bool {
            let mut output: bool = <bool as std::default::Default>::default();
            output = input.cardinality() == ::dafny_runtime::int!(8);
            return output;
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
                    write!(
                        _formatter,
                        "SimpleSmithyDoubleOperations_Compile.Config.Config"
                    )?;
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
