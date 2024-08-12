#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod r#union {
        pub mod internaldafny {
            pub use crate::simple::r#union::internaldafny::types::ISimpleUnionClient;
            pub use dafny_runtime::UpcastObject;
            pub use std::any::Any;

            pub struct _default {}

            impl _default {
                pub fn DefaultSimpleUnionConfig(
                ) -> ::std::rc::Rc<crate::simple::r#union::internaldafny::types::SimpleUnionConfig>
                {
                    ::std::rc::Rc::new(crate::simple::r#union::internaldafny::types::SimpleUnionConfig::SimpleUnionConfig {})
                }
                pub fn SimpleUnion(
                    config: &::std::rc::Rc<
                        crate::simple::r#union::internaldafny::types::SimpleUnionConfig,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            crate::simple::r#union::internaldafny::SimpleUnionClient,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                > {
                    let mut res = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::dafny_runtime::Object<
                                    crate::simple::r#union::internaldafny::SimpleUnionClient,
                                >,
                                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                            >,
                        >,
                    >::new();
                    let mut client = ::dafny_runtime::MaybePlacebo::<
                        ::dafny_runtime::Object<
                            crate::simple::r#union::internaldafny::SimpleUnionClient,
                        >,
                    >::new();
                    let mut _nw0: ::dafny_runtime::Object<
                        crate::simple::r#union::internaldafny::SimpleUnionClient,
                    > = crate::simple::r#union::internaldafny::SimpleUnionClient::_allocate_object(
                    );
                    crate::simple::r#union::internaldafny::SimpleUnionClient::_ctor(
                        &_nw0,
                        &::std::rc::Rc::new(crate::r#_SimpleUnionImpl_Compile::Config::Config {}),
                    );
                    client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                    res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                        crate::r#_Wrappers_Compile::Result::<
                            ::dafny_runtime::Object<
                                crate::simple::r#union::internaldafny::SimpleUnionClient,
                            >,
                            ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                        >::Success {
                            value: client.read(),
                        },
                    ));
                    return res.read();
                }
                pub fn CreateSuccessOfClient(
                    client: &::dafny_runtime::Object<
                        dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                > {
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                        ::dafny_runtime::Object<
                            dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >::Success {
                        value: client.clone(),
                    })
                }
                pub fn CreateFailureOfError(
                    error: &::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                > {
                    ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                        ::dafny_runtime::Object<
                            dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >::Failure {
                        error: error.clone(),
                    })
                }
            }

            pub struct SimpleUnionClient {
                pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleUnionImpl_Compile::Config>,
            }

            impl SimpleUnionClient {
                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                    ::dafny_runtime::allocate_object::<Self>()
                }
                pub fn _ctor(
                    this: &::dafny_runtime::Object<
                        crate::simple::r#union::internaldafny::SimpleUnionClient,
                    >,
                    config: &::std::rc::Rc<crate::r#_SimpleUnionImpl_Compile::Config>,
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
                pub fn config(&self) -> ::std::rc::Rc<crate::r#_SimpleUnionImpl_Compile::Config> {
                    self.r#__i_config.clone()
                }
            }

            impl UpcastObject<dyn Any> for crate::simple::r#union::internaldafny::SimpleUnionClient {
                ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
            }

            impl ISimpleUnionClient for crate::simple::r#union::internaldafny::SimpleUnionClient {
                fn GetUnion(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::r#union::internaldafny::types::GetUnionInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetUnionOutput>,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::GetUnionOutput,
                                >,
                                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                            >,
                        >,
                    >::new();
                    let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                        ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::GetUnionOutput,
                                >,
                                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                            >,
                        >,
                    >::new();
                    _out0 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleUnionImpl_Compile::_default::GetUnion(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                    return output.read();
                }
                fn GetKnownValueUnion(
                    &mut self,
                    input: &::std::rc::Rc<
                        crate::simple::r#union::internaldafny::types::GetKnownValueUnionInput,
                    >,
                ) -> ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                > {
                    let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput>, ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>>>>::new();
                    let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput>, ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>>>>::new();
                    _out1 = ::dafny_runtime::MaybePlacebo::from(
                        crate::r#_SimpleUnionImpl_Compile::_default::GetKnownValueUnion(
                            &self.config().clone(),
                            input,
                        ),
                    );
                    output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                    return output.read();
                }
            }

            impl UpcastObject<dyn ISimpleUnionClient>
                for crate::simple::r#union::internaldafny::SimpleUnionClient
            {
                ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::r#union::internaldafny::types::ISimpleUnionClient);
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
                                write!(_formatter, "simple.union.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                pub enum GetKnownValueUnionInput {
                    GetKnownValueUnionInput {
                        r#union: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::KnownValueUnion,
                                >,
                            >,
                        >,
                    },
                }

                impl GetKnownValueUnionInput {
                    pub fn r#union(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<
                                crate::simple::r#union::internaldafny::types::KnownValueUnion,
                            >,
                        >,
                    > {
                        match self {
                            GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => r#union,
                        }
                    }
                }

                impl Debug for GetKnownValueUnionInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetKnownValueUnionInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => {
                                write!(_formatter, "simple.union.internaldafny.types.GetKnownValueUnionInput.GetKnownValueUnionInput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetKnownValueUnionInput {}

                impl Hash for GetKnownValueUnionInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => {
                                ::std::hash::Hash::hash(r#union, _state)
                            }
                        }
                    }
                }

                impl Default for GetKnownValueUnionInput {
                    fn default() -> GetKnownValueUnionInput {
                        GetKnownValueUnionInput::GetKnownValueUnionInput {
                            r#union: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetKnownValueUnionInput> for &GetKnownValueUnionInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetKnownValueUnionOutput {
                    GetKnownValueUnionOutput {
                        r#union: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::KnownValueUnion,
                                >,
                            >,
                        >,
                    },
                }

                impl GetKnownValueUnionOutput {
                    pub fn r#union(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<
                                crate::simple::r#union::internaldafny::types::KnownValueUnion,
                            >,
                        >,
                    > {
                        match self {
                            GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => {
                                r#union
                            }
                        }
                    }
                }

                impl Debug for GetKnownValueUnionOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetKnownValueUnionOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => {
                                write!(_formatter, "simple.union.internaldafny.types.GetKnownValueUnionOutput.GetKnownValueUnionOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetKnownValueUnionOutput {}

                impl Hash for GetKnownValueUnionOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => {
                                ::std::hash::Hash::hash(r#union, _state)
                            }
                        }
                    }
                }

                impl Default for GetKnownValueUnionOutput {
                    fn default() -> GetKnownValueUnionOutput {
                        GetKnownValueUnionOutput::GetKnownValueUnionOutput {
                            r#union: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetKnownValueUnionOutput> for &GetKnownValueUnionOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetUnionInput {
                    GetUnionInput {
                        r#union: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::MyUnion,
                                >,
                            >,
                        >,
                    },
                }

                impl GetUnionInput {
                    pub fn r#union(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<crate::simple::r#union::internaldafny::types::MyUnion>,
                        >,
                    > {
                        match self {
                            GetUnionInput::GetUnionInput { r#union } => r#union,
                        }
                    }
                }

                impl Debug for GetUnionInput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetUnionInput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetUnionInput::GetUnionInput { r#union } => {
                                write!(
                                    _formatter,
                                    "simple.union.internaldafny.types.GetUnionInput.GetUnionInput("
                                )?;
                                ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetUnionInput {}

                impl Hash for GetUnionInput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetUnionInput::GetUnionInput { r#union } => {
                                ::std::hash::Hash::hash(r#union, _state)
                            }
                        }
                    }
                }

                impl Default for GetUnionInput {
                    fn default() -> GetUnionInput {
                        GetUnionInput::GetUnionInput {
                            r#union: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetUnionInput> for &GetUnionInput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum GetUnionOutput {
                    GetUnionOutput {
                        r#union: ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<
                                ::std::rc::Rc<
                                    crate::simple::r#union::internaldafny::types::MyUnion,
                                >,
                            >,
                        >,
                    },
                }

                impl GetUnionOutput {
                    pub fn r#union(
                        &self,
                    ) -> &::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Option<
                            ::std::rc::Rc<crate::simple::r#union::internaldafny::types::MyUnion>,
                        >,
                    > {
                        match self {
                            GetUnionOutput::GetUnionOutput { r#union } => r#union,
                        }
                    }
                }

                impl Debug for GetUnionOutput {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for GetUnionOutput {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            GetUnionOutput::GetUnionOutput { r#union } => {
                                write!(_formatter, "simple.union.internaldafny.types.GetUnionOutput.GetUnionOutput(")?;
                                ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for GetUnionOutput {}

                impl Hash for GetUnionOutput {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            GetUnionOutput::GetUnionOutput { r#union } => {
                                ::std::hash::Hash::hash(r#union, _state)
                            }
                        }
                    }
                }

                impl Default for GetUnionOutput {
                    fn default() -> GetUnionOutput {
                        GetUnionOutput::GetUnionOutput {
                            r#union: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<GetUnionOutput> for &GetUnionOutput {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum KnownValueUnion {
                    Value { Value: i32 },
                }

                impl KnownValueUnion {
                    pub fn Value(&self) -> &i32 {
                        match self {
                            KnownValueUnion::Value { Value } => Value,
                        }
                    }
                }

                impl Debug for KnownValueUnion {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for KnownValueUnion {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            KnownValueUnion::Value { Value } => {
                                write!(
                                    _formatter,
                                    "simple.union.internaldafny.types.KnownValueUnion.Value("
                                )?;
                                ::dafny_runtime::DafnyPrint::fmt_print(Value, _formatter, false)?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for KnownValueUnion {}

                impl Hash for KnownValueUnion {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            KnownValueUnion::Value { Value } => {
                                ::std::hash::Hash::hash(Value, _state)
                            }
                        }
                    }
                }

                impl Default for KnownValueUnion {
                    fn default() -> KnownValueUnion {
                        KnownValueUnion::Value {
                            Value: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<KnownValueUnion> for &KnownValueUnion {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum MyUnion {
                    IntegerValue {
                        IntegerValue: i32,
                    },
                    StringValue {
                        StringValue: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    },
                }

                impl MyUnion {
                    pub fn IntegerValue(&self) -> &i32 {
                        match self {
                            MyUnion::IntegerValue { IntegerValue } => IntegerValue,
                            MyUnion::StringValue { StringValue } => {
                                panic!("field does not exist on this variant")
                            }
                        }
                    }
                    pub fn StringValue(
                        &self,
                    ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                    {
                        match self {
                            MyUnion::IntegerValue { IntegerValue } => {
                                panic!("field does not exist on this variant")
                            }
                            MyUnion::StringValue { StringValue } => StringValue,
                        }
                    }
                }

                impl Debug for MyUnion {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for MyUnion {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            MyUnion::IntegerValue { IntegerValue } => {
                                write!(
                                    _formatter,
                                    "simple.union.internaldafny.types.MyUnion.IntegerValue("
                                )?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    IntegerValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                            MyUnion::StringValue { StringValue } => {
                                write!(
                                    _formatter,
                                    "simple.union.internaldafny.types.MyUnion.StringValue("
                                )?;
                                ::dafny_runtime::DafnyPrint::fmt_print(
                                    StringValue,
                                    _formatter,
                                    false,
                                )?;
                                write!(_formatter, ")")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for MyUnion {}

                impl Hash for MyUnion {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            MyUnion::IntegerValue { IntegerValue } => {
                                ::std::hash::Hash::hash(IntegerValue, _state)
                            }
                            MyUnion::StringValue { StringValue } => {
                                ::std::hash::Hash::hash(StringValue, _state)
                            }
                        }
                    }
                }

                impl Default for MyUnion {
                    fn default() -> MyUnion {
                        MyUnion::IntegerValue {
                            IntegerValue: ::std::default::Default::default(),
                        }
                    }
                }

                impl AsRef<MyUnion> for &MyUnion {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                pub struct ISimpleUnionClientCallHistory {}

                impl ISimpleUnionClientCallHistory {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                }

                impl UpcastObject<dyn Any>
                    for crate::simple::r#union::internaldafny::types::ISimpleUnionClientCallHistory
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                pub trait ISimpleUnionClient:
                    ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                {
                    fn GetUnion(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::r#union::internaldafny::types::GetUnionInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::r#union::internaldafny::types::GetUnionOutput,
                            >,
                            ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                        >,
                    >;
                    fn GetKnownValueUnion(&mut self, input: &::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetKnownValueUnionInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput>, ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>>>;
                }

                #[derive(PartialEq, Clone)]
                pub enum SimpleUnionConfig {
                    SimpleUnionConfig {},
                }

                impl SimpleUnionConfig {}

                impl Debug for SimpleUnionConfig {
                    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                        ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                    }
                }

                impl DafnyPrint for SimpleUnionConfig {
                    fn fmt_print(
                        &self,
                        _formatter: &mut ::std::fmt::Formatter,
                        _in_seq: bool,
                    ) -> std::fmt::Result {
                        match self {
                            SimpleUnionConfig::SimpleUnionConfig {} => {
                                write!(_formatter, "simple.union.internaldafny.types.SimpleUnionConfig.SimpleUnionConfig")?;
                                Ok(())
                            }
                        }
                    }
                }

                impl Eq for SimpleUnionConfig {}

                impl Hash for SimpleUnionConfig {
                    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                        match self {
                            SimpleUnionConfig::SimpleUnionConfig {} => {}
                        }
                    }
                }

                impl Default for SimpleUnionConfig {
                    fn default() -> SimpleUnionConfig {
                        SimpleUnionConfig::SimpleUnionConfig {}
                    }
                }

                impl AsRef<SimpleUnionConfig> for &SimpleUnionConfig {
                    fn as_ref(&self) -> Self {
                        self
                    }
                }

                #[derive(PartialEq, Clone)]
                pub enum Error {
                    CollectionOfErrors {
                        list: ::dafny_runtime::Sequence<
                            ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
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
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
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
                                write!(
                                    _formatter,
                                    "simple.union.internaldafny.types.Error.CollectionOfErrors("
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
                                    "simple.union.internaldafny.types.Error.Opaque("
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
                    ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>;
            }
        }
    }
}
pub mod r#_SimpleUnionImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetUnion(
            config: &::std::rc::Rc<crate::r#_SimpleUnionImpl_Compile::Config>,
            input: &::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetUnionInput>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetUnionOutput>,
                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetUnionOutput>,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<
                crate::simple::r#union::internaldafny::types::GetUnionOutput,
            > = ::std::rc::Rc::new(
                crate::simple::r#union::internaldafny::types::GetUnionOutput::GetUnionOutput {
                    r#union: input.r#union().clone(),
                },
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetUnionOutput>,
                    ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetKnownValueUnion(
            config: &::std::rc::Rc<crate::r#_SimpleUnionImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::r#union::internaldafny::types::GetKnownValueUnionInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput,
                >,
                ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput,
                        >,
                        ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput> = ::std::rc::Rc::new(crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput::GetKnownValueUnionOutput {
            r#union: input.r#union().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::r#union::internaldafny::types::GetKnownValueUnionOutput,
                    >,
                    ::std::rc::Rc<crate::simple::r#union::internaldafny::types::Error>,
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
                    write!(_formatter, "SimpleUnionImpl_Compile.Config.Config")?;
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
