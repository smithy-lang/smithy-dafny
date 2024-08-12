#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod resources {
        pub mod internaldafny {
            pub use crate::simple::resources::internaldafny::types::ISimpleResourcesClient;
            pub use dafny_runtime::UpcastObject;
            pub use std::any::Any;

            pub struct _default {}

            impl _default {
                pub fn DefaultSimpleResourcesConfig() -> ::std::rc::Rc<
                    crate::simple::resources::internaldafny::types::SimpleResourcesConfig,
                > {
                    ::std::rc::Rc::new(crate::simple::resources::internaldafny::types::SimpleResourcesConfig::SimpleResourcesConfig {
              name: ::dafny_runtime::string_utf16_of("default")
            })
                }
                pub fn SimpleResources(
                    config: &::std::rc::Rc<
                        crate::simple::resources::internaldafny::types::SimpleResourcesConfig,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::resources::internaldafny::SimpleResourcesClient,
                        >,
                        ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                    >,
                > {
                    let mut res = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::dafny_runtime::Object<
                                    crate::simple::resources::internaldafny::SimpleResourcesClient,
                                >,
                                ::std::rc::Rc<
                                    crate::simple::resources::internaldafny::types::Error,
                                >,
                            >,
                        >,
                    >::new();
                    let mut internalConfig: ::std::rc::Rc<
                        crate::r#_SimpleResourcesOperations_Compile::Config,
                    > = ::std::rc::Rc::new(
                        crate::r#_SimpleResourcesOperations_Compile::Config::Config {
                            name: config.name().clone(),
                        },
                    );
                    if crate::r#_SimpleResourcesOperations_Compile::_default::r#_ValidInternalConfig_q(&internalConfig) {
            let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<crate::simple::resources::internaldafny::SimpleResourcesClient>>::new();
            let mut _nw1: ::dafny_runtime::Object<crate::simple::resources::internaldafny::SimpleResourcesClient> = crate::simple::resources::internaldafny::SimpleResourcesClient::_allocate_object();
            crate::simple::resources::internaldafny::SimpleResourcesClient::_ctor(&_nw1, &internalConfig);
            client = ::dafny_runtime::MaybePlacebo::from(_nw1.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::resources::internaldafny::SimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
            return res.read();
          } else {
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::resources::internaldafny::SimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>::Failure {
                    error: ::std::rc::Rc::new(crate::simple::resources::internaldafny::types::Error::SimpleResourcesException {
                          message: ::dafny_runtime::string_utf16_of("Length of name must be greater than 0")
                        })
                  }));
            return res.read();
          };
                    return res.read();
                }
                pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>::Success {
              value: client.clone()
            })
                }
                pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>::Failure {
              error: error.clone()
            })
                }
            }

            pub struct SimpleResourcesClient {
                pub r#__i_config:
                    ::std::rc::Rc<crate::r#_SimpleResourcesOperations_Compile::Config>,
            }

            impl SimpleResourcesClient {
                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                    ::dafny_runtime::allocate_object::<Self>()
                }
                pub fn _ctor(
                    this: &::dafny_runtime::Object<
                        crate::simple::resources::internaldafny::SimpleResourcesClient,
                    >,
                    config: &::std::rc::Rc<crate::r#_SimpleResourcesOperations_Compile::Config>,
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
                ) -> ::std::rc::Rc<crate::r#_SimpleResourcesOperations_Compile::Config>
                {
                    self.r#__i_config.clone()
                }
            }

            impl UpcastObject<dyn Any> for crate::simple::resources::internaldafny::SimpleResourcesClient {
                ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
            }

            impl ISimpleResourcesClient for crate::simple::resources::internaldafny::SimpleResourcesClient {
                fn GetResources(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::resources::internaldafny::types::GetResourcesInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::resources::internaldafny::types::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourcesOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>>::new();
                    let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourcesOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>>::new();
                    _out1 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleResourcesOperations_Compile::_default::GetResources(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                    return output.read();
                }
            }

            impl UpcastObject<dyn ISimpleResourcesClient>
                for crate::simple::resources::internaldafny::SimpleResourcesClient
            {
                ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::resources::internaldafny::types::ISimpleResourcesClient);
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
                                write!(_formatter, "simple.resources.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl<I: ::dafny_runtime::DafnyType + Eq, O: ::dafny_runtime::DafnyType + Eq> Eq
                    for DafnyCallEvent<I, O>
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
                pub enum GetResourceDataInput {
                    GetResourceDataInput {
                        blobValue: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        >,
                        booleanValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                        stringValue: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                        integerValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                        longValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>,
                    },
                }

                impl GetResourceDataInput {
                    pub fn blobValue(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                    > {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => blobValue,
                        }
                    }
                    pub fn booleanValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                    {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => booleanValue,
                        }
                    }
                    pub fn stringValue(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => stringValue,
                        }
                    }
                    pub fn integerValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                    {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => integerValue,
                        }
                    }
                    pub fn longValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>
                    {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => longValue,
                        }
                    }
                }

                impl Debug for GetResourceDataInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetResourceDataInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => {
                                write!(_formatter, "simple.resources.internaldafny.types.GetResourceDataInput.GetResourceDataInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    blobValue, _formatter, false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    booleanValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    stringValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    integerValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    longValue, _formatter, false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetResourceDataInput {}

                impl Hash for GetResourceDataInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetResourceDataInput::GetResourceDataInput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => {
                                ::std::hash::Hash::hash(blobValue, _state);
                                ::std::hash::Hash::hash(booleanValue, _state);
                                ::std::hash::Hash::hash(stringValue, _state);
                                ::std::hash::Hash::hash(integerValue, _state);
                                ::std::hash::Hash::hash(longValue, _state)
                            }
                        }
                    }
                }

                impl Default for GetResourceDataInput {
                    fn default() -> GetResourceDataInput {
                        GetResourceDataInput::GetResourceDataInput {
                            blobValue: ::std::default::Default::default(),
                            booleanValue: ::std::default::Default::default(),
                            stringValue: ::std::default::Default::default(),
                            integerValue: ::std::default::Default::default(),
                            longValue: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetResourceDataInput> for &GetResourceDataInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetResourceDataOutput {
                    GetResourceDataOutput {
                        blobValue: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        >,
                        booleanValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                        stringValue: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                        integerValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                        longValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>,
                    },
                }

                impl GetResourceDataOutput {
                    pub fn blobValue(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                    > {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => blobValue,
                        }
                    }
                    pub fn booleanValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                    {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => booleanValue,
                        }
                    }
                    pub fn stringValue(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => stringValue,
                        }
                    }
                    pub fn integerValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                    {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => integerValue,
                        }
                    }
                    pub fn longValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i64>>
                    {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => longValue,
                        }
                    }
                }

                impl Debug for GetResourceDataOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetResourceDataOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => {
                                write!(_formatter, "simple.resources.internaldafny.types.GetResourceDataOutput.GetResourceDataOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    blobValue, _formatter, false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    booleanValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    stringValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    integerValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    longValue, _formatter, false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetResourceDataOutput {}

                impl Hash for GetResourceDataOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetResourceDataOutput::GetResourceDataOutput {
                                blobValue,
                                booleanValue,
                                stringValue,
                                integerValue,
                                longValue,
                            } => {
                                ::std::hash::Hash::hash(blobValue, _state);
                                ::std::hash::Hash::hash(booleanValue, _state);
                                ::std::hash::Hash::hash(stringValue, _state);
                                ::std::hash::Hash::hash(integerValue, _state);
                                ::std::hash::Hash::hash(longValue, _state)
                            }
                        }
                    }
                }

                impl Default for GetResourceDataOutput {
                    fn default() -> GetResourceDataOutput {
                        GetResourceDataOutput::GetResourceDataOutput {
                            blobValue: ::std::default::Default::default(),
                            booleanValue: ::std::default::Default::default(),
                            stringValue: ::std::default::Default::default(),
                            integerValue: ::std::default::Default::default(),
                            longValue: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetResourceDataOutput> for &GetResourceDataOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetResourcesInput {
                    GetResourcesInput {
                        value: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl GetResourcesInput {
                    pub fn value(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            GetResourcesInput::GetResourcesInput { value } => value,
                        }
                    }
                }

                impl Debug for GetResourcesInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetResourcesInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetResourcesInput::GetResourcesInput { value } => {
                                write!(_formatter, "simple.resources.internaldafny.types.GetResourcesInput.GetResourcesInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetResourcesInput {}

                impl Hash for GetResourcesInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetResourcesInput::GetResourcesInput { value } => {
                                ::std::hash::Hash::hash(value, _state)
                            }
                        }
                    }
                }

                impl Default for GetResourcesInput {
                    fn default() -> GetResourcesInput {
                        GetResourcesInput::GetResourcesInput {
                            value: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetResourcesInput> for &GetResourcesInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetResourcesOutput {
                    GetResourcesOutput {
                        output: ::dafny_runtime::Object<
                            dyn crate::simple::resources::internaldafny::types::ISimpleResource,
                        >,
                    },
                }

                impl GetResourcesOutput {
                    pub fn output(
                        &self,
                    ) -> &::dafny_runtime::Object<
                        dyn crate::simple::resources::internaldafny::types::ISimpleResource,
                    > {
                        match self {
                            GetResourcesOutput::GetResourcesOutput { output } => output,
                        }
                    }
                }

                impl Debug for GetResourcesOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetResourcesOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetResourcesOutput::GetResourcesOutput { output } => {
                                write!(_formatter, "simple.resources.internaldafny.types.GetResourcesOutput.GetResourcesOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetResourcesOutput {}

                impl Hash for GetResourcesOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetResourcesOutput::GetResourcesOutput { output } => {
                                ::std::hash::Hash::hash(output, _state)
                            }
                        }
                    }
                }

                impl Default for GetResourcesOutput {
                    fn default() -> GetResourcesOutput {
                        GetResourcesOutput::GetResourcesOutput {
                            output: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetResourcesOutput> for &GetResourcesOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                pub struct ISimpleResourceCallHistory {}

                impl ISimpleResourceCallHistory {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                }

                impl UpcastObject<dyn Any>
                    for crate::simple::resources::internaldafny::types::ISimpleResourceCallHistory
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                pub trait ISimpleResource:
                    ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                {
                    fn GetResourceData(&mut self, input: &::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(crate::simple::resources::internaldafny::types::ISimpleResource::r#_GetResourceData_k(::dafny_runtime::md!(::dafny_runtime::Object::<_>::from_ref(self)), input));
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn r#_GetResourceData_k(&mut self, input: &::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataOutput>, ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>>>;
                }

                pub struct ISimpleResourcesClientCallHistory {}

                impl ISimpleResourcesClientCallHistory {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                }

                impl UpcastObject<dyn Any>
          for crate::simple::resources::internaldafny::types::ISimpleResourcesClientCallHistory {
          ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
        }

                pub trait ISimpleResourcesClient:
                    ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                {
                    fn GetResources(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::resources::internaldafny::types::GetResourcesInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::resources::internaldafny::types::GetResourcesOutput,
                            >,
                            ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                        >,
                    >;
                }

                #[derive(PartialEq, Clone)]
                pub enum SimpleResourcesConfig {
                    SimpleResourcesConfig {
                        name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    },
                }

                impl SimpleResourcesConfig {
                    pub fn name(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            SimpleResourcesConfig::SimpleResourcesConfig { name } => name,
                        }
                    }
                }

                impl Debug for SimpleResourcesConfig {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for SimpleResourcesConfig {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            SimpleResourcesConfig::SimpleResourcesConfig { name } => {
                                write!(_formatter, "simple.resources.internaldafny.types.SimpleResourcesConfig.SimpleResourcesConfig(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(name, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for SimpleResourcesConfig {}

                impl Hash for SimpleResourcesConfig {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            SimpleResourcesConfig::SimpleResourcesConfig { name } => {
                                ::std::hash::Hash::hash(name, _state)
                            }
                        }
                    }
                }

                impl Default for SimpleResourcesConfig {
                    fn default() -> SimpleResourcesConfig {
                        SimpleResourcesConfig::SimpleResourcesConfig {
                            name: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<SimpleResourcesConfig> for &SimpleResourcesConfig {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum Error {
                    SimpleResourcesException {
                        message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    },
                    CollectionOfErrors {
                        list: ::dafny_runtime::Sequence<
                            ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                        >,
                        message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    },
                    Opaque {
                        obj: ::dafny_runtime::Object<dyn::std::any::Any>,
                    },
                }

                impl Error {
                    pub fn message(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            Error::SimpleResourcesException { message } => message,
                            Error::CollectionOfErrors { list, message } => message,
                            Error::Opaque { obj } => panic!("field does not exist on this variant"),
                        }
                    }
                    pub fn list(
                        &self,
                    ) -> &::dafny_runtime::Sequence<
                        ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                    > {
                        match self {
                            Error::SimpleResourcesException { message } => {
                                panic!("field does not exist on this variant")
                            }
                            Error::CollectionOfErrors { list, message } => list,
                            Error::Opaque { obj } => panic!("field does not exist on this variant"),
                        }
                    }
                    pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
                        match self {
                            Error::SimpleResourcesException { message } => {
                                panic!("field does not exist on this variant")
                            }
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
                            Error::SimpleResourcesException { message } => {
                                write!(_formatter, "simple.resources.internaldafny.types.Error.SimpleResourcesException(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                            Error::CollectionOfErrors { list, message } => {
                                write!(_formatter, "simple.resources.internaldafny.types.Error.CollectionOfErrors(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                            Error::Opaque { obj } => {
                                write!(
                                    _formatter,
                                    "simple.resources.internaldafny.types.Error.Opaque("
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
                            Error::SimpleResourcesException { message } => {
                                ::std::hash::Hash::hash(message, _state)
                            }
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
                        Error::SimpleResourcesException {
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
                    ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>;
            }
        }
    }
}
pub mod r#_SimpleResource_Compile {
    pub use crate::simple::resources::internaldafny::types::ISimpleResource;
    pub use dafny_runtime::UpcastObject;
    pub use std::any::Any;

    pub struct SimpleResource {
        pub r#__i_value: ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        >,
        pub r#__i_name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
    }

    impl SimpleResource {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<crate::r#_SimpleResource_Compile::SimpleResource>,
            value: &::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            name: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> () {
            let mut _set__i_value: bool = false;
            let mut _set__i_name: bool = false;
            ::dafny_runtime::update_field_uninit_object!(
                this.clone(),
                r#__i_value,
                _set__i_value,
                value.clone()
            );
            ::dafny_runtime::update_field_uninit_object!(
                this.clone(),
                r#__i_name,
                _set__i_name,
                name.clone()
            );
            return ();
        }
        pub fn value(
            &self,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            self.r#__i_value.clone()
        }
        pub fn name(&self) -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            self.r#__i_name.clone()
        }
    }

    impl UpcastObject<dyn Any> for SimpleResource {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    impl ISimpleResource for SimpleResource {
        fn r#_GetResourceData_k(
            &mut self,
            input: &::std::rc::Rc<
                crate::simple::resources::internaldafny::types::GetResourceDataInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::resources::internaldafny::types::GetResourceDataOutput,
                >,
                ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::resources::internaldafny::types::GetResourceDataOutput,
                        >,
                        ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut rtnString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = if matches!(
                input.stringValue().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                self.name()
                    .clone()
                    .concat(&::dafny_runtime::string_utf16_of(" "))
                    .concat(input.stringValue().value())
            } else {
                self.name().clone()
            };
            let mut rtn: ::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourceDataOutput> = ::std::rc::Rc::new(crate::simple::resources::internaldafny::types::GetResourceDataOutput::GetResourceDataOutput {
            blobValue: input.blobValue().clone(),
            booleanValue: input.booleanValue().clone(),
            stringValue: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: rtnString.clone()
                }),
            integerValue: input.integerValue().clone(),
            longValue: input.longValue().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::resources::internaldafny::types::GetResourceDataOutput,
                    >,
                    ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                >::Success {
                    value: rtn.clone(),
                },
            ));
            return output.read();
        }
    }

    impl UpcastObject<dyn ISimpleResource> for SimpleResource {
        ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::resources::internaldafny::types::ISimpleResource);
    }
}
pub mod r#_SimpleResourcesOperations_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn r#_ValidInternalConfig_q(
            config: &::std::rc::Rc<crate::r#_SimpleResourcesOperations_Compile::Config>,
        ) -> bool {
            true && ::dafny_runtime::int!(0) < config.name().cardinality()
        }
        pub fn GetResources(
            config: &::std::rc::Rc<crate::r#_SimpleResourcesOperations_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::resources::internaldafny::types::GetResourcesInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourcesOutput>,
                ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::resources::internaldafny::types::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<crate::r#_SimpleResource_Compile::SimpleResource>,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<
                crate::r#_SimpleResource_Compile::SimpleResource,
            > = crate::r#_SimpleResource_Compile::SimpleResource::_allocate_object();
            crate::r#_SimpleResource_Compile::SimpleResource::_ctor(
                &_nw0,
                input.value(),
                config.name(),
            );
            resource = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            let mut result: ::std::rc::Rc<crate::simple::resources::internaldafny::types::GetResourcesOutput> = ::std::rc::Rc::new(crate::simple::resources::internaldafny::types::GetResourcesOutput::GetResourcesOutput {
            output: ::dafny_runtime::upcast_object::<crate::r#_SimpleResource_Compile::SimpleResource, dyn crate::simple::resources::internaldafny::types::ISimpleResource>()(resource.read())
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::resources::internaldafny::types::GetResourcesOutput,
                    >,
                    ::std::rc::Rc<crate::simple::resources::internaldafny::types::Error>,
                >::Success {
                    value: result.clone(),
                },
            ));
            return output.read();
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Config {
        Config {
            name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
    }

    impl Config {
        pub fn name(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                Config::Config { name } => name,
            }
        }
    }

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
                Config::Config { name } => {
                    write!(
                        _formatter,
                        "SimpleResourcesOperations_Compile.Config.Config("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(name, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Config {}

    impl Hash for Config {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Config::Config { name } => ::std::hash::Hash::hash(name, _state),
            }
        }
    }

    impl Default for Config {
        fn default() -> Config {
            Config::Config {
                name: ::std::default::Default::default(),
            }
        }
    }

    impl AsRef<Config> for &Config {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod _module {}
