#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod refinement {
        pub mod internaldafny {
            pub use crate::simple::refinement::internaldafny::types::ISimpleRefinementClient;
            pub use dafny_runtime::UpcastObject;
            pub use std::any::Any;

            pub struct _default {}

            impl _default {
                pub fn DefaultSimpleRefinementConfig() -> ::std::rc::Rc<
                    crate::simple::refinement::internaldafny::types::SimpleRefinementConfig,
                > {
                    ::std::rc::Rc::new(crate::simple::refinement::internaldafny::types::SimpleRefinementConfig::SimpleRefinementConfig {})
                }
                pub fn SimpleRefinement(
                    config: &::std::rc::Rc<
                        crate::simple::refinement::internaldafny::types::SimpleRefinementConfig,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::refinement::internaldafny::SimpleRefinementClient,
                        >,
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                > {
                    let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::refinement::internaldafny::SimpleRefinementClient>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>>::new();
                    let mut client = ::dafny_runtime::MaybePlacebo::<
                        ::dafny_runtime::Object<
                            crate::simple::refinement::internaldafny::SimpleRefinementClient,
                        >,
                    >::new();
                    let mut _nw0: ::dafny_runtime::Object<crate::simple::refinement::internaldafny::SimpleRefinementClient> = crate::simple::refinement::internaldafny::SimpleRefinementClient::_allocate_object();
                    crate::simple::refinement::internaldafny::SimpleRefinementClient::_ctor(
                        &_nw0,
                        &::std::rc::Rc::new(
                            crate::r#_SimpleRefinementImpl_Compile::Config::Config {},
                        ),
                    );
                    client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                    res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                        crate::r#_Wrappers_Compile::Result::<
                            ::dafny_runtime::Object<
                                crate::simple::refinement::internaldafny::SimpleRefinementClient,
                            >,
                            ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                        >::Success {
                            value: client.read(),
                        },
                    ));
                    return res.read();
                }
                pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>::Success {
              value: client.clone()
            })
                }
                pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>{
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>::Failure {
              error: error.clone()
            })
                }
            }

            pub struct SimpleRefinementClient {
                pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
            }

            impl SimpleRefinementClient {
                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                    ::dafny_runtime::allocate_object::<Self>()
                }
                pub fn _ctor(
                    this: &::dafny_runtime::Object<
                        crate::simple::refinement::internaldafny::SimpleRefinementClient,
                    >,
                    config: &::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
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
                ) -> ::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config> {
                    self.r#__i_config.clone()
                }
            }

            impl UpcastObject<dyn Any> for crate::simple::refinement::internaldafny::SimpleRefinementClient {
                ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
            }

            impl ISimpleRefinementClient for crate::simple::refinement::internaldafny::SimpleRefinementClient {
                fn GetRefinement(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::refinement::internaldafny::types::GetRefinementInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::refinement::internaldafny::types::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>>::new();
                    let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>>::new();
                    _out0 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleRefinementImpl_Compile::_default::GetRefinement(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                    return output.read();
                }
                fn OnlyInput(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::refinement::internaldafny::types::OnlyInputInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                (),
                                ::std::rc::Rc<
                                    crate::simple::refinement::internaldafny::types::Error,
                                >,
                            >,
                        >,
                    >::new();
                    let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                (),
                                ::std::rc::Rc<
                                    crate::simple::refinement::internaldafny::types::Error,
                                >,
                            >,
                        >,
                    >::new();
                    _out1 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleRefinementImpl_Compile::_default::OnlyInput(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                    return output.read();
                }
                fn OnlyOutput(
                    &mut self,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::refinement::internaldafny::types::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::OnlyOutputOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>>::new();
                    let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::OnlyOutputOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>>::new();
                    _out2 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleRefinementImpl_Compile::_default::OnlyOutput(
                            &self.config().clone(),
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
                    return output.read();
                }
                fn ReadonlyOperation(&self, input: &::std::rc::Rc<crate::simple::refinement::internaldafny::types::ReadonlyOperationInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::ReadonlyOperationOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>{
                    crate::r#_SimpleRefinementImpl_Compile::_default::ReadonlyOperation(
                        &self.config().clone(),
                        input,
                    )
                }
            }

            impl UpcastObject<dyn ISimpleRefinementClient>
                for crate::simple::refinement::internaldafny::SimpleRefinementClient
            {
                ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::refinement::internaldafny::types::ISimpleRefinementClient);
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
                                write!(_formatter, "simple.refinement.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                pub enum GetRefinementInput {
                    GetRefinementInput {
                        requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        optionalString: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl GetRefinementInput {
                    pub fn requiredString(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            GetRefinementInput::GetRefinementInput {
                                requiredString,
                                optionalString,
                            } => requiredString,
                        }
                    }
                    pub fn optionalString(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            GetRefinementInput::GetRefinementInput {
                                requiredString,
                                optionalString,
                            } => optionalString,
                        }
                    }
                }

                impl Debug for GetRefinementInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetRefinementInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetRefinementInput::GetRefinementInput {
                                requiredString,
                                optionalString,
                            } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.GetRefinementInput.GetRefinementInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    requiredString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    optionalString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetRefinementInput {}

                impl Hash for GetRefinementInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetRefinementInput::GetRefinementInput {
                                requiredString,
                                optionalString,
                            } => {
                                ::std::hash::Hash::hash(requiredString, _state);
                                ::std::hash::Hash::hash(optionalString, _state)
                            }
                        }
                    }
                }

                impl Default for GetRefinementInput {
                    fn default() -> GetRefinementInput {
                        GetRefinementInput::GetRefinementInput {
                            requiredString: ::std::default::Default::default(),
                            optionalString: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetRefinementInput> for &GetRefinementInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetRefinementOutput {
                    GetRefinementOutput {
                        requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        optionalString: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl GetRefinementOutput {
                    pub fn requiredString(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            GetRefinementOutput::GetRefinementOutput {
                                requiredString,
                                optionalString,
                            } => requiredString,
                        }
                    }
                    pub fn optionalString(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            GetRefinementOutput::GetRefinementOutput {
                                requiredString,
                                optionalString,
                            } => optionalString,
                        }
                    }
                }

                impl Debug for GetRefinementOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetRefinementOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetRefinementOutput::GetRefinementOutput {
                                requiredString,
                                optionalString,
                            } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.GetRefinementOutput.GetRefinementOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    requiredString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    optionalString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetRefinementOutput {}

                impl Hash for GetRefinementOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetRefinementOutput::GetRefinementOutput {
                                requiredString,
                                optionalString,
                            } => {
                                ::std::hash::Hash::hash(requiredString, _state);
                                ::std::hash::Hash::hash(optionalString, _state)
                            }
                        }
                    }
                }

                impl Default for GetRefinementOutput {
                    fn default() -> GetRefinementOutput {
                        GetRefinementOutput::GetRefinementOutput {
                            requiredString: ::std::default::Default::default(),
                            optionalString: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetRefinementOutput> for &GetRefinementOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum OnlyInputInput {
                    OnlyInputInput {
                        value: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl OnlyInputInput {
                    pub fn value(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            OnlyInputInput::OnlyInputInput { value } => value,
                        }
                    }
                }

                impl Debug for OnlyInputInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for OnlyInputInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            OnlyInputInput::OnlyInputInput { value } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.OnlyInputInput.OnlyInputInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for OnlyInputInput {}

                impl Hash for OnlyInputInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            OnlyInputInput::OnlyInputInput { value } => {
                                ::std::hash::Hash::hash(value, _state)
                            }
                        }
                    }
                }

                impl Default for OnlyInputInput {
                    fn default() -> OnlyInputInput {
                        OnlyInputInput::OnlyInputInput {
                            value: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<OnlyInputInput> for &OnlyInputInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum OnlyOutputOutput {
                    OnlyOutputOutput {
                        value: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl OnlyOutputOutput {
                    pub fn value(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            OnlyOutputOutput::OnlyOutputOutput { value } => value,
                        }
                    }
                }

                impl Debug for OnlyOutputOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for OnlyOutputOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            OnlyOutputOutput::OnlyOutputOutput { value } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.OnlyOutputOutput.OnlyOutputOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for OnlyOutputOutput {}

                impl Hash for OnlyOutputOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            OnlyOutputOutput::OnlyOutputOutput { value } => {
                                ::std::hash::Hash::hash(value, _state)
                            }
                        }
                    }
                }

                impl Default for OnlyOutputOutput {
                    fn default() -> OnlyOutputOutput {
                        OnlyOutputOutput::OnlyOutputOutput {
                            value: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<OnlyOutputOutput> for &OnlyOutputOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum ReadonlyOperationInput {
                    ReadonlyOperationInput {
                        requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        optionalString: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl ReadonlyOperationInput {
                    pub fn requiredString(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            ReadonlyOperationInput::ReadonlyOperationInput {
                                requiredString,
                                optionalString,
                            } => requiredString,
                        }
                    }
                    pub fn optionalString(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            ReadonlyOperationInput::ReadonlyOperationInput {
                                requiredString,
                                optionalString,
                            } => optionalString,
                        }
                    }
                }

                impl Debug for ReadonlyOperationInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for ReadonlyOperationInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            ReadonlyOperationInput::ReadonlyOperationInput {
                                requiredString,
                                optionalString,
                            } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.ReadonlyOperationInput.ReadonlyOperationInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    requiredString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    optionalString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for ReadonlyOperationInput {}

                impl Hash for ReadonlyOperationInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            ReadonlyOperationInput::ReadonlyOperationInput {
                                requiredString,
                                optionalString,
                            } => {
                                ::std::hash::Hash::hash(requiredString, _state);
                                ::std::hash::Hash::hash(optionalString, _state)
                            }
                        }
                    }
                }

                impl Default for ReadonlyOperationInput {
                    fn default() -> ReadonlyOperationInput {
                        ReadonlyOperationInput::ReadonlyOperationInput {
                            requiredString: ::std::default::Default::default(),
                            optionalString: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<ReadonlyOperationInput> for &ReadonlyOperationInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum ReadonlyOperationOutput {
                    ReadonlyOperationOutput {
                        requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        optionalString: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >,
                        >,
                    },
                }

                impl ReadonlyOperationOutput {
                    pub fn requiredString(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            ReadonlyOperationOutput::ReadonlyOperationOutput {
                                requiredString,
                                optionalString,
                            } => requiredString,
                        }
                    }
                    pub fn optionalString(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        >,
                    > {
                        match self {
                            ReadonlyOperationOutput::ReadonlyOperationOutput {
                                requiredString,
                                optionalString,
                            } => optionalString,
                        }
                    }
                }

                impl Debug for ReadonlyOperationOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for ReadonlyOperationOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            ReadonlyOperationOutput::ReadonlyOperationOutput {
                                requiredString,
                                optionalString,
                            } => {
                                write!(_formatter, "simple.refinement.internaldafny.types.ReadonlyOperationOutput.ReadonlyOperationOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    requiredString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    optionalString,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for ReadonlyOperationOutput {}

                impl Hash for ReadonlyOperationOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            ReadonlyOperationOutput::ReadonlyOperationOutput {
                                requiredString,
                                optionalString,
                            } => {
                                ::std::hash::Hash::hash(requiredString, _state);
                                ::std::hash::Hash::hash(optionalString, _state)
                            }
                        }
                    }
                }

                impl Default for ReadonlyOperationOutput {
                    fn default() -> ReadonlyOperationOutput {
                        ReadonlyOperationOutput::ReadonlyOperationOutput {
                            requiredString: ::std::default::Default::default(),
                            optionalString: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<ReadonlyOperationOutput> for &ReadonlyOperationOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                pub struct ISimpleRefinementClientCallHistory {}

                impl ISimpleRefinementClientCallHistory {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                }

                impl UpcastObject<dyn Any>
          for crate::simple::refinement::internaldafny::types::ISimpleRefinementClientCallHistory {
          ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
        }

                pub trait ISimpleRefinementClient:
                    ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                {
                    fn GetRefinement(&mut self, input: &::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>;
                    fn OnlyInput(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::refinement::internaldafny::types::OnlyInputInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            (),
                            ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                        >,
                    >;
                    fn OnlyOutput(
                        &mut self,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::refinement::internaldafny::types::OnlyOutputOutput,
                            >,
                            ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                        >,
                    >;
                    fn ReadonlyOperation(&self, input: &::std::rc::Rc<crate::simple::refinement::internaldafny::types::ReadonlyOperationInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::refinement::internaldafny::types::ReadonlyOperationOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>>;
                }

                #[derive(PartialEq, Clone)]
                pub enum SimpleRefinementConfig {
                    SimpleRefinementConfig {},
                }

                impl SimpleRefinementConfig {}

                impl Debug for SimpleRefinementConfig {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for SimpleRefinementConfig {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            SimpleRefinementConfig::SimpleRefinementConfig {} => {
                                write!(_formatter, "simple.refinement.internaldafny.types.SimpleRefinementConfig.SimpleRefinementConfig")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for SimpleRefinementConfig {}

                impl Hash for SimpleRefinementConfig {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            SimpleRefinementConfig::SimpleRefinementConfig {} => {}
                        }
                    }
                }

                impl Default for SimpleRefinementConfig {
                    fn default() -> SimpleRefinementConfig {
                        SimpleRefinementConfig::SimpleRefinementConfig {}
                    }
                }

                impl AsRef<SimpleRefinementConfig> for &SimpleRefinementConfig {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum Error {
                    CollectionOfErrors {
                        list: ::dafny_runtime::Sequence<
                            ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
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
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
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
                                write!(_formatter, "simple.refinement.internaldafny.types.Error.CollectionOfErrors(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                                write!(_formatter, ", ")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                            Error::Opaque { obj } => {
                                write!(
                                    _formatter,
                                    "simple.refinement.internaldafny.types.Error.Opaque("
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
                    ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>;
            }
        }
    }
}
pub mod r#_SimpleRefinementImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetRefinement(
            config: &::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::refinement::internaldafny::types::GetRefinementInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementOutput>,
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::refinement::internaldafny::types::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::refinement::internaldafny::types::GetRefinementOutput> = ::std::rc::Rc::new(crate::simple::refinement::internaldafny::types::GetRefinementOutput::GetRefinementOutput {
            requiredString: input.requiredString().clone(),
            optionalString: input.optionalString().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::refinement::internaldafny::types::GetRefinementOutput,
                    >,
                    ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn OnlyInput(
            config: &::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<crate::simple::refinement::internaldafny::types::OnlyInputInput>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                (),
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(input));
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    (),
                    ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                >::Success {
                    value: (),
                },
            ));
            return output.read();
        }
        pub fn OnlyOutput(
            config: &::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::OnlyOutputOutput>,
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::refinement::internaldafny::types::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::refinement::internaldafny::types::OnlyOutputOutput> = ::std::rc::Rc::new(crate::simple::refinement::internaldafny::types::OnlyOutputOutput::OnlyOutputOutput {
            value: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("Hello World")
                })
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::refinement::internaldafny::types::OnlyOutputOutput,
                    >,
                    ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn ReadonlyOperation(
            config: &::std::rc::Rc<crate::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::refinement::internaldafny::types::ReadonlyOperationInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::refinement::internaldafny::types::ReadonlyOperationOutput,
                >,
                ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::std::rc::Rc<crate::simple::refinement::internaldafny::types::ReadonlyOperationOutput>, ::std::rc::Rc<crate::simple::refinement::internaldafny::types::Error>>::Success {
          value: ::std::rc::Rc::new(crate::simple::refinement::internaldafny::types::ReadonlyOperationOutput::ReadonlyOperationOutput {
                requiredString: input.requiredString().clone(),
                optionalString: input.optionalString().clone()
              })
        })
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
                    write!(_formatter, "SimpleRefinementImpl_Compile.Config.Config")?;
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
