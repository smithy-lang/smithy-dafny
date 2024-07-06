#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_drefinement_dinternaldafny_dtypes {
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
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
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
                    input.hash(_state);
                    output.hash(_state)
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
    pub enum GetRefinementInput {
        GetRefinementInput {
            requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            optionalString: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetRefinementInput {
        pub fn requiredString(
            &self,
        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
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
            super::r#_Wrappers_Compile::Option<
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

    impl ::std::fmt::Debug for GetRefinementInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetRefinementInput {
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
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.GetRefinementInput.GetRefinementInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(requiredString, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(optionalString, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetRefinementInput {}

    impl ::std::hash::Hash for GetRefinementInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetRefinementInput::GetRefinementInput {
                    requiredString,
                    optionalString,
                } => {
                    requiredString.hash(_state);
                    optionalString.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetRefinementInput {
        fn default() -> GetRefinementInput {
            GetRefinementInput::GetRefinementInput {
                requiredString: ::std::default::Default::default(),
                optionalString: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetRefinementInput> for &GetRefinementInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetRefinementOutput {
        GetRefinementOutput {
            requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            optionalString: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetRefinementOutput {
        pub fn requiredString(
            &self,
        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
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
            super::r#_Wrappers_Compile::Option<
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

    impl ::std::fmt::Debug for GetRefinementOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetRefinementOutput {
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
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.GetRefinementOutput.GetRefinementOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(requiredString, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(optionalString, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetRefinementOutput {}

    impl ::std::hash::Hash for GetRefinementOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetRefinementOutput::GetRefinementOutput {
                    requiredString,
                    optionalString,
                } => {
                    requiredString.hash(_state);
                    optionalString.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetRefinementOutput {
        fn default() -> GetRefinementOutput {
            GetRefinementOutput::GetRefinementOutput {
                requiredString: ::std::default::Default::default(),
                optionalString: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetRefinementOutput> for &GetRefinementOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum OnlyInputInput {
        OnlyInputInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl OnlyInputInput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                OnlyInputInput::OnlyInputInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for OnlyInputInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for OnlyInputInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                OnlyInputInput::OnlyInputInput { value } => {
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.OnlyInputInput.OnlyInputInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for OnlyInputInput {}

    impl ::std::hash::Hash for OnlyInputInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                OnlyInputInput::OnlyInputInput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for OnlyInputInput {
        fn default() -> OnlyInputInput {
            OnlyInputInput::OnlyInputInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<OnlyInputInput> for &OnlyInputInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum OnlyOutputOutput {
        OnlyOutputOutput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl OnlyOutputOutput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                OnlyOutputOutput::OnlyOutputOutput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for OnlyOutputOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for OnlyOutputOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                OnlyOutputOutput::OnlyOutputOutput { value } => {
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.OnlyOutputOutput.OnlyOutputOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for OnlyOutputOutput {}

    impl ::std::hash::Hash for OnlyOutputOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                OnlyOutputOutput::OnlyOutputOutput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for OnlyOutputOutput {
        fn default() -> OnlyOutputOutput {
            OnlyOutputOutput::OnlyOutputOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<OnlyOutputOutput> for &OnlyOutputOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum ReadonlyOperationInput {
        ReadonlyOperationInput {
            requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            optionalString: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl ReadonlyOperationInput {
        pub fn requiredString(
            &self,
        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
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
            super::r#_Wrappers_Compile::Option<
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

    impl ::std::fmt::Debug for ReadonlyOperationInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for ReadonlyOperationInput {
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
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.ReadonlyOperationInput.ReadonlyOperationInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(requiredString, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(optionalString, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for ReadonlyOperationInput {}

    impl ::std::hash::Hash for ReadonlyOperationInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                ReadonlyOperationInput::ReadonlyOperationInput {
                    requiredString,
                    optionalString,
                } => {
                    requiredString.hash(_state);
                    optionalString.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for ReadonlyOperationInput {
        fn default() -> ReadonlyOperationInput {
            ReadonlyOperationInput::ReadonlyOperationInput {
                requiredString: ::std::default::Default::default(),
                optionalString: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<ReadonlyOperationInput> for &ReadonlyOperationInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum ReadonlyOperationOutput {
        ReadonlyOperationOutput {
            requiredString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            optionalString: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl ReadonlyOperationOutput {
        pub fn requiredString(
            &self,
        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
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
            super::r#_Wrappers_Compile::Option<
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

    impl ::std::fmt::Debug for ReadonlyOperationOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for ReadonlyOperationOutput {
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
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.ReadonlyOperationOutput.ReadonlyOperationOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(requiredString, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(optionalString, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for ReadonlyOperationOutput {}

    impl ::std::hash::Hash for ReadonlyOperationOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                ReadonlyOperationOutput::ReadonlyOperationOutput {
                    requiredString,
                    optionalString,
                } => {
                    requiredString.hash(_state);
                    optionalString.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for ReadonlyOperationOutput {
        fn default() -> ReadonlyOperationOutput {
            ReadonlyOperationOutput::ReadonlyOperationOutput {
                requiredString: ::std::default::Default::default(),
                optionalString: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<ReadonlyOperationOutput> for &ReadonlyOperationOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleRefinementClientCallHistory {}

    impl ISimpleRefinementClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleRefinementClient {
        fn GetRefinement(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn OnlyInput(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyInputInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                (),
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn OnlyOutput(
            &mut self,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput>,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn ReadonlyOperation(
            &self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleRefinementConfig {
        SimpleRefinementConfig {},
    }

    impl SimpleRefinementConfig {}

    impl ::std::fmt::Debug for SimpleRefinementConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleRefinementConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleRefinementConfig::SimpleRefinementConfig {} => {
                    write!(_formatter, "r#_simple_drefinement_dinternaldafny_dtypes.SimpleRefinementConfig.SimpleRefinementConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleRefinementConfig {}

    impl ::std::hash::Hash for SimpleRefinementConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleRefinementConfig::SimpleRefinementConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleRefinementConfig {
        fn default() -> SimpleRefinementConfig {
            SimpleRefinementConfig::SimpleRefinementConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleRefinementConfig> for &SimpleRefinementConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
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
                        "r#_simple_drefinement_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_drefinement_dinternaldafny_dtypes.Error.Opaque("
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
                    list.hash(_state);
                    message.hash(_state)
                }
                Error::Opaque { obj } => obj.hash(_state),
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

    pub type OpaqueError = ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleRefinementImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetRefinement(
            config: &::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput> = ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput::GetRefinementOutput {
            requiredString: input.requiredString().clone(),
            optionalString: input.optionalString().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput::GetRefinementOutput {
            requiredString: input.requiredString().clone(),
            optionalString: input.optionalString().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn OnlyInput(
            config: &::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyInputInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                (),
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            print!("{}", ::dafny_runtime::DafnyPrintWrapper(input));
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    (),
                    ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: (),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn OnlyOutput(
            config: &::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput>,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput> = ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput::OnlyOutputOutput {
            value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("Hello World")
                })
          });
            res = ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput::OnlyOutputOutput {
            value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: ::dafny_runtime::string_utf16_of("Hello World")
                })
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn ReadonlyOperation(
            config: &::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput>, ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>>::Success {
          value: ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput::ReadonlyOperationOutput {
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
                    write!(_formatter, "r#_SimpleRefinementImpl_Compile.Config.Config")?;
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
pub mod r#_simple_drefinement_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleRefinementConfig(
        ) -> ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::SimpleRefinementConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_drefinement_dinternaldafny_dtypes::SimpleRefinementConfig::SimpleRefinementConfig {})
        }
        pub fn SimpleRefinement(
            config: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::SimpleRefinementConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient> = super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient::_allocate_rcmut();
            super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleRefinementImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >::Success {
                value: client.clone(),
            })
        }
        pub fn CreateFailureOfError(
            error: &::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >::Failure {
                error: error.clone(),
            })
        }
    }

    pub struct SimpleRefinementClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
    }

    impl SimpleRefinementClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config>,
        ) -> () {
            let mut _set__i_config: bool = false;
            ::dafny_runtime::update_field_uninit_rcmut!(
                this.clone(),
                r#__i_config,
                _set__i_config,
                config.clone()
            );
            return ();
        }
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleRefinementImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_drefinement_dinternaldafny_dtypes::ISimpleRefinementClient
        for super::r#_simple_drefinement_dinternaldafny::SimpleRefinementClient
    {
        fn GetRefinement(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::GetRefinementOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleRefinementImpl_Compile::_default::GetRefinement(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn OnlyInput(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyInputInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                (),
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        (),
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleRefinementImpl_Compile::_default::OnlyInput(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
        fn OnlyOutput(
            &mut self,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput>,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_drefinement_dinternaldafny_dtypes::OnlyOutputOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleRefinementImpl_Compile::_default::OnlyOutput(&self.config()),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
        fn ReadonlyOperation(
            &self,
            input: &::std::rc::Rc<
                super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_drefinement_dinternaldafny_dtypes::ReadonlyOperationOutput,
                >,
                ::std::rc::Rc<super::r#_simple_drefinement_dinternaldafny_dtypes::Error>,
            >,
        > {
            super::r#_SimpleRefinementImpl_Compile::_default::ReadonlyOperation(
                &self.config(),
                input,
            )
        }
    }
}
pub mod _module {}
