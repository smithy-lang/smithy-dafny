#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod aggregate {
        pub mod internaldafny {
            pub use crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient;
            pub use dafny_runtime::UpcastObject;
            pub use std::any::Any;

            pub struct _default {}

            impl _default {
                pub fn DefaultSimpleAggregateConfig() -> ::std::rc::Rc<
                    crate::simple::aggregate::internaldafny::types::SimpleAggregateConfig,
                > {
                    ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::SimpleAggregateConfig::SimpleAggregateConfig {})
                }
                pub fn SimpleAggregate(
                    config: &::std::rc::Rc<
                        crate::simple::aggregate::internaldafny::types::SimpleAggregateConfig,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::aggregate::internaldafny::SimpleAggregateClient,
                        >,
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    >,
                > {
                    let mut res = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::dafny_runtime::Object<
                                    crate::simple::aggregate::internaldafny::SimpleAggregateClient,
                                >,
                                ::std::rc::Rc<
                                    crate::simple::aggregate::internaldafny::types::Error,
                                >,
                            >,
                        >,
                    >::new();
                    let mut client = ::dafny_runtime::MaybePlacebo::<
                        ::dafny_runtime::Object<
                            crate::simple::aggregate::internaldafny::SimpleAggregateClient,
                        >,
                    >::new();
                    let mut _nw0: ::dafny_runtime::Object<crate::simple::aggregate::internaldafny::SimpleAggregateClient> = crate::simple::aggregate::internaldafny::SimpleAggregateClient::_allocate_object();
                    crate::simple::aggregate::internaldafny::SimpleAggregateClient::_ctor(
                        &_nw0,
                        &::std::rc::Rc::new(
                            crate::r#_SimpleAggregateImpl_Compile::Config::Config {},
                        ),
                    );
                    client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                    res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                        crate::r#_Wrappers_Compile::Result::<
                            ::dafny_runtime::Object<
                                crate::simple::aggregate::internaldafny::SimpleAggregateClient,
                            >,
                            ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                        >::Success {
                            value: client.read(),
                        },
                    ));
                    return res.read();
                }
                pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>::Success {
              value: client.clone()
            })
                }
                pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>::Failure {
              error: error.clone()
            })
                }
            }

            pub struct SimpleAggregateClient {
                pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleAggregateImpl_Compile::Config>,
            }

            impl SimpleAggregateClient {
                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                    ::dafny_runtime::allocate_object::<Self>()
                }
                pub fn _ctor(
                    this: &::dafny_runtime::Object<
                        crate::simple::aggregate::internaldafny::SimpleAggregateClient,
                    >,
                    config: &::std::rc::Rc<crate::r#_SimpleAggregateImpl_Compile::Config>,
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
                ) -> ::std::rc::Rc<crate::r#_SimpleAggregateImpl_Compile::Config> {
                    self.r#__i_config.clone()
                }
            }

            impl UpcastObject<dyn Any> for crate::simple::aggregate::internaldafny::SimpleAggregateClient {
                ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
            }

            impl ISimpleAggregateClient for crate::simple::aggregate::internaldafny::SimpleAggregateClient {
                fn GetAggregate(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::aggregate::internaldafny::types::GetAggregateInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>>::new();
                    let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>>::new();
                    _out0 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleAggregateImpl_Compile::_default::GetAggregate(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                    return output.read();
                }
                fn GetAggregateKnownValueTest(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::aggregate::internaldafny::types::GetAggregateInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>>::new();
                    let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>, ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>>>>::new();
                    _out1 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleAggregateImpl_Compile::_default::GetAggregateKnownValueTest(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                    return output.read();
                }
            }

            impl UpcastObject<dyn ISimpleAggregateClient>
                for crate::simple::aggregate::internaldafny::SimpleAggregateClient
            {
                ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::aggregate::internaldafny::types::ISimpleAggregateClient);
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
                                write!(_formatter, "simple.aggregate.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                pub enum GetAggregateInput {
                    GetAggregateInput {
            simpleStringList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
            structureList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>>>>,
            simpleStringMap: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
            simpleIntegerMap: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32>>>,
            nestedStructure: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::NestedStructure>>>
          }
        }

                impl GetAggregateInput {
                    pub fn simpleStringList(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleStringList,
                        }
                    }
                    pub fn structureList(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>>>>{
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => structureList,
                        }
                    }
                    pub fn simpleStringMap(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Map<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleStringMap,
                        }
                    }
                    pub fn simpleIntegerMap(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Map<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                i32,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleIntegerMap,
                        }
                    }
                    pub fn nestedStructure(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<
                                crate::simple::aggregate::internaldafny::types::NestedStructure,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => nestedStructure,
                        }
                    }
                }

                impl Debug for GetAggregateInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetAggregateInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.GetAggregateInput.GetAggregateInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleStringList,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    structureList,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleStringMap,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleIntegerMap,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    nestedStructure,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetAggregateInput {}

                impl Hash for GetAggregateInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetAggregateInput::GetAggregateInput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => {
                                ::std::hash::Hash::hash(simpleStringList, _state);
                                ::std::hash::Hash::hash(structureList, _state);
                                ::std::hash::Hash::hash(simpleStringMap, _state);
                                ::std::hash::Hash::hash(simpleIntegerMap, _state);
                                ::std::hash::Hash::hash(nestedStructure, _state)
                            }
                        }
                    }
                }

                impl Default for GetAggregateInput {
                    fn default() -> GetAggregateInput {
                        GetAggregateInput::GetAggregateInput {
                            simpleStringList: ::std::default::Default::default(),
                            structureList: ::std::default::Default::default(),
                            simpleStringMap: ::std::default::Default::default(),
                            simpleIntegerMap: ::std::default::Default::default(),
                            nestedStructure: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetAggregateInput> for &GetAggregateInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetAggregateOutput {
                    GetAggregateOutput {
            simpleStringList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
            structureList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>>>>,
            simpleStringMap: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
            simpleIntegerMap: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32>>>,
            nestedStructure: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::NestedStructure>>>
          }
        }

                impl GetAggregateOutput {
                    pub fn simpleStringList(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleStringList,
                        }
                    }
                    pub fn structureList(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>>>>{
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => structureList,
                        }
                    }
                    pub fn simpleStringMap(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Map<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleStringMap,
                        }
                    }
                    pub fn simpleIntegerMap(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Map<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                i32,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => simpleIntegerMap,
                        }
                    }
                    pub fn nestedStructure(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<
                                crate::simple::aggregate::internaldafny::types::NestedStructure,
                            >,
                        >,
                    > {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => nestedStructure,
                        }
                    }
                }

                impl Debug for GetAggregateOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetAggregateOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.GetAggregateOutput.GetAggregateOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleStringList,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    structureList,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleStringMap,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    simpleIntegerMap,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    nestedStructure,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetAggregateOutput {}

                impl Hash for GetAggregateOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetAggregateOutput::GetAggregateOutput {
                                simpleStringList,
                                structureList,
                                simpleStringMap,
                                simpleIntegerMap,
                                nestedStructure,
                            } => {
                                ::std::hash::Hash::hash(simpleStringList, _state);
                                ::std::hash::Hash::hash(structureList, _state);
                                ::std::hash::Hash::hash(simpleStringMap, _state);
                                ::std::hash::Hash::hash(simpleIntegerMap, _state);
                                ::std::hash::Hash::hash(nestedStructure, _state)
                            }
                        }
                    }
                }

                impl Default for GetAggregateOutput {
                    fn default() -> GetAggregateOutput {
                        GetAggregateOutput::GetAggregateOutput {
                            simpleStringList: ::std::default::Default::default(),
                            structureList: ::std::default::Default::default(),
                            simpleStringMap: ::std::default::Default::default(),
                            simpleIntegerMap: ::std::default::Default::default(),
                            nestedStructure: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetAggregateOutput> for &GetAggregateOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum NestedStructure {
                    NestedStructure {
                        stringStructure: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::std::rc::Rc<
                                    crate::simple::aggregate::internaldafny::types::StringStructure,
                                >,
                            >,
                        >,
                    },
                }

                impl NestedStructure {
                    pub fn stringStructure(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<
                                crate::simple::aggregate::internaldafny::types::StringStructure,
                            >,
                        >,
                    > {
                        match self {
                            NestedStructure::NestedStructure { stringStructure } => stringStructure,
                        }
                    }
                }

                impl Debug for NestedStructure {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for NestedStructure {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            NestedStructure::NestedStructure { stringStructure } => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.NestedStructure.NestedStructure(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    stringStructure,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for NestedStructure {}

                impl Hash for NestedStructure {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            NestedStructure::NestedStructure { stringStructure } => {
                                ::std::hash::Hash::hash(stringStructure, _state)
                            }
                        }
                    }
                }

                impl Default for NestedStructure {
                    fn default() -> NestedStructure {
                        NestedStructure::NestedStructure {
                            stringStructure: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<NestedStructure> for &NestedStructure {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                pub struct ISimpleAggregateClientCallHistory {}

                impl ISimpleAggregateClientCallHistory {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                }

                impl UpcastObject<dyn Any>
          for crate::simple::aggregate::internaldafny::types::ISimpleAggregateClientCallHistory {
          ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
        }

                pub trait ISimpleAggregateClient:
                    ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                {
                    fn GetAggregate(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                            >,
                            ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                        >,
                    >;
                    fn GetAggregateKnownValueTest(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                            >,
                            ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                        >,
                    >;
                }

                #[derive(PartialEq, Clone)]
                pub enum SimpleAggregateConfig {
                    SimpleAggregateConfig {},
                }

                impl SimpleAggregateConfig {}

                impl Debug for SimpleAggregateConfig {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for SimpleAggregateConfig {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            SimpleAggregateConfig::SimpleAggregateConfig {} => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.SimpleAggregateConfig.SimpleAggregateConfig")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for SimpleAggregateConfig {}

                impl Hash for SimpleAggregateConfig {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            SimpleAggregateConfig::SimpleAggregateConfig {} => {}
                        }
                    }
                }

                impl Default for SimpleAggregateConfig {
                    fn default() -> SimpleAggregateConfig {
                        SimpleAggregateConfig::SimpleAggregateConfig {}
                    }
                }

                impl AsRef<SimpleAggregateConfig> for &SimpleAggregateConfig {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum StringStructure {
                    StringStructure {
                        value: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl StringStructure {
                    pub fn value(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            StringStructure::StringStructure { value } => value,
                        }
                    }
                }

                impl Debug for StringStructure {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for StringStructure {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            StringStructure::StringStructure { value } => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.StringStructure.StringStructure(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for StringStructure {}

                impl Hash for StringStructure {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            StringStructure::StringStructure { value } => {
                                ::std::hash::Hash::hash(value, _state)
                            }
                        }
                    }
                }

                impl Default for StringStructure {
                    fn default() -> StringStructure {
                        StringStructure::StringStructure {
                            value: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<StringStructure> for &StringStructure {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum StructureListElement {
                    StructureListElement {
                        stringValue: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                        integerValue: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                    },
                }

                impl StructureListElement {
                    pub fn stringValue(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            StructureListElement::StructureListElement {
                                stringValue,
                                integerValue,
                            } => stringValue,
                        }
                    }
                    pub fn integerValue(
                        &self,
                    ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                    {
                        match self {
                            StructureListElement::StructureListElement {
                                stringValue,
                                integerValue,
                            } => integerValue,
                        }
                    }
                }

                impl Debug for StructureListElement {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for StructureListElement {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            StructureListElement::StructureListElement {
                                stringValue,
                                integerValue,
                            } => {
                                write!(_formatter, "simple.aggregate.internaldafny.types.StructureListElement.StructureListElement(")?;
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
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for StructureListElement {}

                impl Hash for StructureListElement {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            StructureListElement::StructureListElement {
                                stringValue,
                                integerValue,
                            } => {
                                ::std::hash::Hash::hash(stringValue, _state);
                                ::std::hash::Hash::hash(integerValue, _state)
                            }
                        }
                    }
                }

                impl Default for StructureListElement {
                    fn default() -> StructureListElement {
                        StructureListElement::StructureListElement {
                            stringValue: ::std::default::Default::default(),
                            integerValue: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<StructureListElement> for &StructureListElement {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum Error {
                    CollectionOfErrors {
                        list: ::dafny_runtime::Sequence<
                            ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
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
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    > {
                        match self {
                            Error::CollectionOfErrors { list, message } => list,
                            Error::Opaque { obj } => panic!("field does not exist on this variant"),
                        }
                    }
                    pub fn message(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
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
                                write!(_formatter, "simple.aggregate.internaldafny.types.Error.CollectionOfErrors(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                            Error::Opaque { obj } => {
                                write!(
                                    _formatter,
                                    "simple.aggregate.internaldafny.types.Error.Opaque("
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
                    ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>;
            }
        }
    }
}
pub mod r#_SimpleAggregateImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetAggregate(
            config: &::std::rc::Rc<crate::r#_SimpleAggregateImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::aggregate::internaldafny::types::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>,
                ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput> = ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                    >,
                    ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetAggregateKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleAggregateImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::aggregate::internaldafny::types::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput>,
                ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            crate::r#_SimpleAggregateImpl_Compile::_default::ValidateInput(input);
            let mut res: ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::GetAggregateOutput> = ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::aggregate::internaldafny::types::GetAggregateOutput,
                    >,
                    ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn ValidateInput(
            input: &::std::rc::Rc<
                crate::simple::aggregate::internaldafny::types::GetAggregateInput,
            >,
        ) -> () {
            let mut _e00: ::dafny_runtime::Sequence<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = input.simpleStringList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >),
            );
            let mut _e10: ::dafny_runtime::Sequence<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::seq![::dafny_runtime::string_utf16_of("Test")];
            if !(_e00.clone() == _e10.clone()) {
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
            let mut _e01: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = input.simpleStringMap().UnwrapOr(&::dafny_runtime::map![]);
            let mut _e11: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test1")) => (::dafny_runtime::string_utf16_of("Success"))];
            if !(_e01.clone() == _e11.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e01));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e11));
                panic!("Halt")
            };
            let mut _e02: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                i32,
            > = input.simpleIntegerMap().UnwrapOr(&::dafny_runtime::map![]);
            let mut _e12: ::dafny_runtime::Map<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                i32,
            > = ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test3")) => (3)];
            if !(_e02.clone() == _e12.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e02));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e12));
                panic!("Halt")
            };
            let mut _e03: ::dafny_runtime::Sequence<
                ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>,
            > = input.structureList().UnwrapOr(
                &(::dafny_runtime::seq![]
                    as ::dafny_runtime::Sequence<
                        ::std::rc::Rc<
                            crate::simple::aggregate::internaldafny::types::StructureListElement,
                        >,
                    >),
            );
            let mut _e13: ::dafny_runtime::Sequence<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StructureListElement>> = ::dafny_runtime::seq![::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::StructureListElement::StructureListElement {
              stringValue: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                    value: ::dafny_runtime::string_utf16_of("Test2")
                  }),
              integerValue: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<i32>::Some {
                    value: 2
                  })
            })];
            if !(_e03.clone() == _e13.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e03));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e13));
                panic!("Halt")
            };
            let mut _e04: ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::NestedStructure> = input.nestedStructure().UnwrapOr(&::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::NestedStructure::NestedStructure {
              stringStructure: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StringStructure>>::Some {
                    value: ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::StringStructure::StringStructure {
                          value: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                                value: ::dafny_runtime::string_utf16_of("")
                              })
                        })
                  })
            }));
            let mut _e14: ::std::rc::Rc<crate::simple::aggregate::internaldafny::types::NestedStructure> = ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::NestedStructure::NestedStructure {
            stringStructure: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::simple::aggregate::internaldafny::types::StringStructure>>::Some {
                  value: ::std::rc::Rc::new(crate::simple::aggregate::internaldafny::types::StringStructure::StringStructure {
                        value: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                              value: ::dafny_runtime::string_utf16_of("Nested")
                            })
                      })
                })
          });
            if !(_e04.clone() == _e14.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e04));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e14));
                panic!("Halt")
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
                    write!(_formatter, "SimpleAggregateImpl_Compile.Config.Config")?;
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
