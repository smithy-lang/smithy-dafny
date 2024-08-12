#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod smithyenum {
            pub mod internaldafny {
                pub use crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleEnumConfig() -> ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig,
                    > {
                        ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig::SimpleEnumConfig {})
                    }
                    pub fn SimpleEnum(
                        config: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig>,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                            >,
                            ::std::rc::Rc<
                                crate::simple::types::smithyenum::internaldafny::types::Error,
                            >,
                        >,
                    > {
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                            >,
                        >::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient> = crate::simple::types::smithyenum::internaldafny::SimpleEnumClient::_allocate_object();
                        crate::simple::types::smithyenum::internaldafny::SimpleEnumClient::_ctor(
                            &_nw0,
                            &::std::rc::Rc::new(
                                crate::r#_SimpleEnumImpl_Compile::Config::Config {},
                            ),
                        );
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleEnumClient {
                    pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
                }

                impl SimpleEnumClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any> for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesEnumClient for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient {
                    fn GetEnum(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnum(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn GetEnumFirstKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumFirstKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                    fn GetEnumSecondKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out2 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumSecondKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
                        return output.read();
                    }
                    fn GetEnumThirdKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out3 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumThirdKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out3.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesEnumClient>
                    for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient);
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
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetEnumInput {
                        GetEnumInput {
              value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>
            }
          }

                    impl GetEnumInput {
                        pub fn value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>{
                            match self {
                                GetEnumInput::GetEnumInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetEnumInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetEnumInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetEnumInput::GetEnumInput { value } => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.GetEnumInput.GetEnumInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetEnumInput {}

                    impl Hash for GetEnumInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetEnumInput::GetEnumInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetEnumInput {
                        fn default() -> GetEnumInput {
                            GetEnumInput::GetEnumInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetEnumInput> for &GetEnumInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetEnumOutput {
                        GetEnumOutput {
              value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>
            }
          }

                    impl GetEnumOutput {
                        pub fn value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>{
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetEnumOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetEnumOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.GetEnumOutput.GetEnumOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetEnumOutput {}

                    impl Hash for GetEnumOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetEnumOutput {
                        fn default() -> GetEnumOutput {
                            GetEnumOutput::GetEnumOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetEnumOutput> for &GetEnumOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleEnumConfig {
                        SimpleEnumConfig {},
                    }

                    impl SimpleEnumConfig {}

                    impl Debug for SimpleEnumConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleEnumConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleEnumConfig::SimpleEnumConfig {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumConfig.SimpleEnumConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleEnumConfig {}

                    impl Hash for SimpleEnumConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleEnumConfig::SimpleEnumConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleEnumConfig {
                        fn default() -> SimpleEnumConfig {
                            SimpleEnumConfig::SimpleEnumConfig {}
                        }
                    }

                    impl AsRef<SimpleEnumConfig> for &SimpleEnumConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleEnumShape {
                        FIRST {},
                        SECOND {},
                        THIRD {},
                    }

                    impl SimpleEnumShape {}

                    impl Debug for SimpleEnumShape {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleEnumShape {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleEnumShape::FIRST {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.FIRST")?;
                                    Ok(())
                                }
                                SimpleEnumShape::SECOND {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.SECOND")?;
                                    Ok(())
                                }
                                SimpleEnumShape::THIRD {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.THIRD")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleEnumShape {}

                    impl Hash for SimpleEnumShape {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleEnumShape::FIRST {} => {}
                                SimpleEnumShape::SECOND {} => {}
                                SimpleEnumShape::THIRD {} => {}
                            }
                        }
                    }

                    impl Default for SimpleEnumShape {
                        fn default() -> SimpleEnumShape {
                            SimpleEnumShape::FIRST {}
                        }
                    }

                    impl AsRef<SimpleEnumShape> for &SimpleEnumShape {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesEnumClientCallHistory {}

                    impl ISimpleTypesEnumClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesEnumClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetEnum(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumFirstKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumSecondKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumThirdKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::smithyenum::internaldafny::types::Error,
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
                                crate::simple::types::smithyenum::internaldafny::types::Error,
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
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                        "simple.types.smithyenum.internaldafny.types.Error.Opaque("
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
                        crate::simple::types::smithyenum::internaldafny::types::Error,
                    >;
                }
            }
        }
    }
}
pub mod r#_SimpleEnumImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetEnum(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumFirstKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
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
            let mut _e00: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e10: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {},
            );
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
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e01: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e11: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {},
            );
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
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumSecondKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
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
            let mut _e02: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e12: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {},
            );
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
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e03: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e13: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {},
            );
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
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumThirdKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
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
            let mut _e04: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e14: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {},
            );
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
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e05: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e15: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {},
            );
            if !(_e05.clone() == _e15.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e05));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e15));
                panic!("Halt")
            };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
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
                    write!(_formatter, "SimpleEnumImpl_Compile.Config.Config")?;
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
