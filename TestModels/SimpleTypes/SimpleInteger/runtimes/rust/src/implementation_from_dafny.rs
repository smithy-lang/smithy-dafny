#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod integer {
            pub mod internaldafny {
                pub use crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleIntegerConfig() -> ::std::rc::Rc<
                        crate::simple::types::integer::internaldafny::types::SimpleIntegerConfig,
                    > {
                        ::std::rc::Rc::new(crate::simple::types::integer::internaldafny::types::SimpleIntegerConfig::SimpleIntegerConfig {})
                    }
                    pub fn SimpleInteger(
                        config: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::SimpleIntegerConfig>,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::dafny_runtime::Object<
                                crate::simple::types::integer::internaldafny::SimpleIntegerClient,
                            >,
                            ::std::rc::Rc<
                                crate::simple::types::integer::internaldafny::types::Error,
                            >,
                        >,
                    > {
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::integer::internaldafny::SimpleIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<
                            ::dafny_runtime::Object<
                                crate::simple::types::integer::internaldafny::SimpleIntegerClient,
                            >,
                        >::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::integer::internaldafny::SimpleIntegerClient> = crate::simple::types::integer::internaldafny::SimpleIntegerClient::_allocate_object();
                        crate::simple::types::integer::internaldafny::SimpleIntegerClient::_ctor(
                            &_nw0,
                            &::std::rc::Rc::new(
                                crate::r#_SimpleIntegerImpl_Compile::Config::Config {},
                            ),
                        );
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::integer::internaldafny::SimpleIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleIntegerClient {
                    pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleIntegerImpl_Compile::Config>,
                }

                impl SimpleIntegerClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::integer::internaldafny::SimpleIntegerClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleIntegerImpl_Compile::Config>,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleIntegerImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any> for crate::simple::types::integer::internaldafny::SimpleIntegerClient {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesIntegerClient
                    for crate::simple::types::integer::internaldafny::SimpleIntegerClient
                {
                    fn GetInteger(&mut self, input: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleIntegerImpl_Compile::_default::GetInteger(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn GetIntegerKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleIntegerImpl_Compile::_default::GetIntegerKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesIntegerClient>
                    for crate::simple::types::integer::internaldafny::SimpleIntegerClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClient);
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
                                    write!(_formatter, "simple.types.integer.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetIntegerInput {
                        GetIntegerInput {
                            value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                        },
                    }

                    impl GetIntegerInput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                        {
                            match self {
                                GetIntegerInput::GetIntegerInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetIntegerInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetIntegerInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetIntegerInput::GetIntegerInput { value } => {
                                    write!(_formatter, "simple.types.integer.internaldafny.types.GetIntegerInput.GetIntegerInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetIntegerInput {}

                    impl Hash for GetIntegerInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetIntegerInput::GetIntegerInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetIntegerInput {
                        fn default() -> GetIntegerInput {
                            GetIntegerInput::GetIntegerInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetIntegerInput> for &GetIntegerInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetIntegerOutput {
                        GetIntegerOutput {
                            value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                        },
                    }

                    impl GetIntegerOutput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                        {
                            match self {
                                GetIntegerOutput::GetIntegerOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetIntegerOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetIntegerOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetIntegerOutput::GetIntegerOutput { value } => {
                                    write!(_formatter, "simple.types.integer.internaldafny.types.GetIntegerOutput.GetIntegerOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetIntegerOutput {}

                    impl Hash for GetIntegerOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetIntegerOutput::GetIntegerOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetIntegerOutput {
                        fn default() -> GetIntegerOutput {
                            GetIntegerOutput::GetIntegerOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetIntegerOutput> for &GetIntegerOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleIntegerConfig {
                        SimpleIntegerConfig {},
                    }

                    impl SimpleIntegerConfig {}

                    impl Debug for SimpleIntegerConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleIntegerConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleIntegerConfig::SimpleIntegerConfig {} => {
                                    write!(_formatter, "simple.types.integer.internaldafny.types.SimpleIntegerConfig.SimpleIntegerConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleIntegerConfig {}

                    impl Hash for SimpleIntegerConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleIntegerConfig::SimpleIntegerConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleIntegerConfig {
                        fn default() -> SimpleIntegerConfig {
                            SimpleIntegerConfig::SimpleIntegerConfig {}
                        }
                    }

                    impl AsRef<SimpleIntegerConfig> for &SimpleIntegerConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesIntegerClientCallHistory {}

                    impl ISimpleTypesIntegerClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::integer::internaldafny::types::ISimpleTypesIntegerClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesIntegerClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetInteger(&mut self, input: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>;
                        fn GetIntegerKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput>, ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::integer::internaldafny::types::Error,
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
                                crate::simple::types::integer::internaldafny::types::Error,
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
                                    write!(_formatter, "simple.types.integer.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                        "simple.types.integer.internaldafny.types.Error.Opaque("
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
                        ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>;
                }
            }
        }
    }
}
pub mod r#_SimpleIntegerImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetInteger(
            config: &::std::rc::Rc<crate::r#_SimpleIntegerImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::integer::internaldafny::types::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                >,
                ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(::dafny_runtime::truncate!(::dafny_runtime::int!(0) - crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT(), i32) <= input.value().UnwrapOr(&0) && input.value().UnwrapOr(&0) <= ::dafny_runtime::truncate!(crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::INT32_MAX_LIMIT() - ::dafny_runtime::int!(1), i32)) {
        panic!("Halt")
      };
            let mut res: ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput> = ::std::rc::Rc::new(crate::simple::types::integer::internaldafny::types::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetIntegerKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleIntegerImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::integer::internaldafny::types::GetIntegerInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                >,
                ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e00: i32 = input.value().UnwrapOr(&0);
            let mut _e10: i32 = 20;
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
            let mut res: ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::GetIntegerOutput> = ::std::rc::Rc::new(crate::simple::types::integer::internaldafny::types::GetIntegerOutput::GetIntegerOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::integer::internaldafny::types::GetIntegerOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::integer::internaldafny::types::Error>,
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
                    write!(_formatter, "SimpleIntegerImpl_Compile.Config.Config")?;
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
