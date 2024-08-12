#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod smithylong {
            pub mod internaldafny {
                pub use crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleLongConfig() -> ::std::rc::Rc<
                        crate::simple::types::smithylong::internaldafny::types::SimpleLongConfig,
                    > {
                        ::std::rc::Rc::new(crate::simple::types::smithylong::internaldafny::types::SimpleLongConfig::SimpleLongConfig {})
                    }
                    pub fn SimpleLong(
                        config: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::SimpleLongConfig>,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithylong::internaldafny::SimpleLongClient,
                            >,
                            ::std::rc::Rc<
                                crate::simple::types::smithylong::internaldafny::types::Error,
                            >,
                        >,
                    > {
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::smithylong::internaldafny::SimpleLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithylong::internaldafny::SimpleLongClient,
                            >,
                        >::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::smithylong::internaldafny::SimpleLongClient> = crate::simple::types::smithylong::internaldafny::SimpleLongClient::_allocate_object();
                        crate::simple::types::smithylong::internaldafny::SimpleLongClient::_ctor(
                            &_nw0,
                            &::std::rc::Rc::new(
                                crate::r#_SimpleLongImpl_Compile::Config::Config {},
                            ),
                        );
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::smithylong::internaldafny::SimpleLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleLongClient {
                    pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleLongImpl_Compile::Config>,
                }

                impl SimpleLongClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::smithylong::internaldafny::SimpleLongClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleLongImpl_Compile::Config>,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleLongImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any> for crate::simple::types::smithylong::internaldafny::SimpleLongClient {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesLongClient for crate::simple::types::smithylong::internaldafny::SimpleLongClient {
                    fn GetLong(&mut self, input: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleLongImpl_Compile::_default::GetLong(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn GetLongKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleLongImpl_Compile::_default::GetLongKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesLongClient>
                    for crate::simple::types::smithylong::internaldafny::SimpleLongClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClient);
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
                                    write!(_formatter, "simple.types.smithylong.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetLongInput {
                        GetLongInput {
                            value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>,
                        },
                    }

                    impl GetLongInput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>
                        {
                            match self {
                                GetLongInput::GetLongInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetLongInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetLongInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetLongInput::GetLongInput { value } => {
                                    write!(_formatter, "simple.types.smithylong.internaldafny.types.GetLongInput.GetLongInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetLongInput {}

                    impl Hash for GetLongInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetLongInput::GetLongInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetLongInput {
                        fn default() -> GetLongInput {
                            GetLongInput::GetLongInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetLongInput> for &GetLongInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetLongOutput {
                        GetLongOutput {
                            value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>,
                        },
                    }

                    impl GetLongOutput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>
                        {
                            match self {
                                GetLongOutput::GetLongOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetLongOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetLongOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetLongOutput::GetLongOutput { value } => {
                                    write!(_formatter, "simple.types.smithylong.internaldafny.types.GetLongOutput.GetLongOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetLongOutput {}

                    impl Hash for GetLongOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetLongOutput::GetLongOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetLongOutput {
                        fn default() -> GetLongOutput {
                            GetLongOutput::GetLongOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetLongOutput> for &GetLongOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleLongConfig {
                        SimpleLongConfig {},
                    }

                    impl SimpleLongConfig {}

                    impl Debug for SimpleLongConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleLongConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleLongConfig::SimpleLongConfig {} => {
                                    write!(_formatter, "simple.types.smithylong.internaldafny.types.SimpleLongConfig.SimpleLongConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleLongConfig {}

                    impl Hash for SimpleLongConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleLongConfig::SimpleLongConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleLongConfig {
                        fn default() -> SimpleLongConfig {
                            SimpleLongConfig::SimpleLongConfig {}
                        }
                    }

                    impl AsRef<SimpleLongConfig> for &SimpleLongConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesLongClientCallHistory {}

                    impl ISimpleTypesLongClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::smithylong::internaldafny::types::ISimpleTypesLongClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesLongClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetLong(&mut self, input: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>;
                        fn GetLongKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput>, ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::smithylong::internaldafny::types::Error,
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
                                crate::simple::types::smithylong::internaldafny::types::Error,
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
                                    write!(_formatter, "simple.types.smithylong.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                        "simple.types.smithylong.internaldafny.types.Error.Opaque("
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

                    pub type OpaqueError = ::std::rc::Rc<
                        crate::simple::types::smithylong::internaldafny::types::Error,
                    >;
                }
            }
        }
    }
}
pub mod r#_SimpleLongImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetLong(
            config: &::std::rc::Rc<crate::r#_SimpleLongImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithylong::internaldafny::types::GetLongInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithylong::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleLongImpl_Compile::_default::ValidateLongType(
                input.value().value().clone(),
            );
            let mut res: ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput> = ::std::rc::Rc::new(crate::simple::types::smithylong::internaldafny::types::GetLongOutput::GetLongOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleLongImpl_Compile::_default::ValidateLongType(
                res.value().value().clone(),
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetLongKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleLongImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithylong::internaldafny::types::GetLongInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithylong::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleLongImpl_Compile::_default::ValidateLongType(
                input.value().value().clone(),
            );
            let mut _e00: i64 = input.value().value().clone();
            let mut _e10: i64 = 33;
            if !(_e00 == _e10) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e00));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e10));
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::GetLongOutput> = ::std::rc::Rc::new(crate::simple::types::smithylong::internaldafny::types::GetLongOutput::GetLongOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleLongImpl_Compile::_default::ValidateLongType(
                res.value().value().clone(),
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithylong::internaldafny::types::GetLongOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithylong::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn ValidateLongType(input: i64) -> () {
            if input >= 0 {
                if input >= ::dafny_runtime::truncate!(crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT(), i64) {
          return ();
        };
                if !(0 < input + ::dafny_runtime::truncate!(crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT(), i64)) {
          panic!("Halt")
        }
            } else {
                if input < 0 {
                    if input < 0 - ::dafny_runtime::truncate!(crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT(), i64) {
            return ();
          };
                    if !(input + (0 - ::dafny_runtime::truncate!(crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT(), i64)) < 0) {
            panic!("Halt")
          }
                } else {
                    if !false {
                        panic!("Halt")
                    }
                }
            };
            return ();
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
                    write!(_formatter, "SimpleLongImpl_Compile.Config.Config")?;
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
