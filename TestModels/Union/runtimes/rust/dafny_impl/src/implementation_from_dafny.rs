#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dunion_dinternaldafny_dtypes {
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
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent("
                    )?;
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
    pub enum GetKnownValueUnionInput {
        GetKnownValueUnionInput {
            r#union: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::KnownValueUnion>,
                >,
            >,
        },
    }

    impl GetKnownValueUnionInput {
        pub fn r#union(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::KnownValueUnion>,
            >,
        > {
            match self {
                GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => r#union,
            }
        }
    }

    impl ::std::fmt::Debug for GetKnownValueUnionInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetKnownValueUnionInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => {
                    write!(_formatter, "r#_simple_dunion_dinternaldafny_dtypes.GetKnownValueUnionInput.GetKnownValueUnionInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetKnownValueUnionInput {}

    impl ::std::hash::Hash for GetKnownValueUnionInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetKnownValueUnionInput::GetKnownValueUnionInput { r#union } => {
                    r#union.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetKnownValueUnionInput {
        fn default() -> GetKnownValueUnionInput {
            GetKnownValueUnionInput::GetKnownValueUnionInput {
                r#union: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetKnownValueUnionInput> for &GetKnownValueUnionInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetKnownValueUnionOutput {
        GetKnownValueUnionOutput {
            r#union: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::KnownValueUnion>,
                >,
            >,
        },
    }

    impl GetKnownValueUnionOutput {
        pub fn r#union(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::KnownValueUnion>,
            >,
        > {
            match self {
                GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => r#union,
            }
        }
    }

    impl ::std::fmt::Debug for GetKnownValueUnionOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetKnownValueUnionOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => {
                    write!(_formatter, "r#_simple_dunion_dinternaldafny_dtypes.GetKnownValueUnionOutput.GetKnownValueUnionOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetKnownValueUnionOutput {}

    impl ::std::hash::Hash for GetKnownValueUnionOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetKnownValueUnionOutput::GetKnownValueUnionOutput { r#union } => {
                    r#union.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetKnownValueUnionOutput {
        fn default() -> GetKnownValueUnionOutput {
            GetKnownValueUnionOutput::GetKnownValueUnionOutput {
                r#union: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetKnownValueUnionOutput> for &GetKnownValueUnionOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetUnionInput {
        GetUnionInput {
            r#union: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::MyUnion>,
                >,
            >,
        },
    }

    impl GetUnionInput {
        pub fn r#union(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::MyUnion>,
            >,
        > {
            match self {
                GetUnionInput::GetUnionInput { r#union } => r#union,
            }
        }
    }

    impl ::std::fmt::Debug for GetUnionInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetUnionInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetUnionInput::GetUnionInput { r#union } => {
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.GetUnionInput.GetUnionInput("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetUnionInput {}

    impl ::std::hash::Hash for GetUnionInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetUnionInput::GetUnionInput { r#union } => r#union.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetUnionInput {
        fn default() -> GetUnionInput {
            GetUnionInput::GetUnionInput {
                r#union: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetUnionInput> for &GetUnionInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetUnionOutput {
        GetUnionOutput {
            r#union: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::MyUnion>,
                >,
            >,
        },
    }

    impl GetUnionOutput {
        pub fn r#union(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::MyUnion>,
            >,
        > {
            match self {
                GetUnionOutput::GetUnionOutput { r#union } => r#union,
            }
        }
    }

    impl ::std::fmt::Debug for GetUnionOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetUnionOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetUnionOutput::GetUnionOutput { r#union } => {
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.GetUnionOutput.GetUnionOutput("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(r#union, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetUnionOutput {}

    impl ::std::hash::Hash for GetUnionOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetUnionOutput::GetUnionOutput { r#union } => r#union.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetUnionOutput {
        fn default() -> GetUnionOutput {
            GetUnionOutput::GetUnionOutput {
                r#union: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetUnionOutput> for &GetUnionOutput {
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

    impl ::std::fmt::Debug for KnownValueUnion {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KnownValueUnion {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KnownValueUnion::Value { Value } => {
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.KnownValueUnion.Value("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KnownValueUnion {}

    impl ::std::hash::Hash for KnownValueUnion {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KnownValueUnion::Value { Value } => Value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for KnownValueUnion {
        fn default() -> KnownValueUnion {
            KnownValueUnion::Value {
                Value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<KnownValueUnion> for &KnownValueUnion {
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
        pub fn StringValue(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                MyUnion::IntegerValue { IntegerValue } => {
                    panic!("field does not exist on this variant")
                }
                MyUnion::StringValue { StringValue } => StringValue,
            }
        }
    }

    impl ::std::fmt::Debug for MyUnion {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for MyUnion {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                MyUnion::IntegerValue { IntegerValue } => {
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.MyUnion.IntegerValue("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(IntegerValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                MyUnion::StringValue { StringValue } => {
                    write!(
                        _formatter,
                        "r#_simple_dunion_dinternaldafny_dtypes.MyUnion.StringValue("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(StringValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for MyUnion {}

    impl ::std::hash::Hash for MyUnion {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                MyUnion::IntegerValue { IntegerValue } => IntegerValue.hash(_state),
                MyUnion::StringValue { StringValue } => StringValue.hash(_state),
            }
        }
    }

    impl ::std::default::Default for MyUnion {
        fn default() -> MyUnion {
            MyUnion::IntegerValue {
                IntegerValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<MyUnion> for &MyUnion {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleUnionClientCallHistory {}

    impl ISimpleUnionClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleUnionClient {
        fn GetUnion(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput>,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetKnownValueUnion(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleUnionConfig {
        SimpleUnionConfig {},
    }

    impl SimpleUnionConfig {}

    impl ::std::fmt::Debug for SimpleUnionConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleUnionConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleUnionConfig::SimpleUnionConfig {} => {
                    write!(_formatter, "r#_simple_dunion_dinternaldafny_dtypes.SimpleUnionConfig.SimpleUnionConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleUnionConfig {}

    impl ::std::hash::Hash for SimpleUnionConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleUnionConfig::SimpleUnionConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleUnionConfig {
        fn default() -> SimpleUnionConfig {
            SimpleUnionConfig::SimpleUnionConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleUnionConfig> for &SimpleUnionConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        Opaque {
            obj: ::dafny_runtime::Object<dyn ::std::any::Any>,
        },
    }

    impl Error {
        pub fn list(
            &self,
        ) -> &::dafny_runtime::Sequence<
            ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
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
        pub fn obj(&self) -> &::dafny_runtime::Object<dyn ::std::any::Any> {
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
                        "r#_simple_dunion_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_dunion_dinternaldafny_dtypes.Error.Opaque("
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

    pub type OpaqueError = ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleUnionImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetUnion(
            config: &::std::rc::Rc<super::r#_SimpleUnionImpl_Compile::Config>,
            input: &::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput>,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<
                super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput,
            > = ::std::rc::Rc::new(
                super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput::GetUnionOutput {
                    union: input.r#union().clone(),
                },
            );
            res = ::std::rc::Rc::new(
                super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput::GetUnionOutput {
                    union: input.r#union().clone(),
                },
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput>,
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetKnownValueUnion(
            config: &::std::rc::Rc<super::r#_SimpleUnionImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput> = ::std::rc::Rc::new(super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput::GetKnownValueUnionOutput {
            union: input.r#union().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput::GetKnownValueUnionOutput {
            union: input.r#union().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
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
                    write!(_formatter, "r#_SimpleUnionImpl_Compile.Config.Config")?;
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
pub mod r#_simple_dunion_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleUnionConfig(
        ) -> ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::SimpleUnionConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_dunion_dinternaldafny_dtypes::SimpleUnionConfig::SimpleUnionConfig {})
        }
        pub fn SimpleUnion(
            config: &::std::rc::Rc<
                super::r#_simple_dunion_dinternaldafny_dtypes::SimpleUnionConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<super::r#_simple_dunion_dinternaldafny::SimpleUnionClient>,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dunion_dinternaldafny::SimpleUnionClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<super::r#_simple_dunion_dinternaldafny::SimpleUnionClient>,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<
                super::r#_simple_dunion_dinternaldafny::SimpleUnionClient,
            > = super::r#_simple_dunion_dinternaldafny::SimpleUnionClient::_allocate_rcmut();
            super::r#_simple_dunion_dinternaldafny::SimpleUnionClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleUnionImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dunion_dinternaldafny::SimpleUnionClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >::Success {
                value: client.clone(),
            })
        }
        pub fn CreateFailureOfError(
            error: &::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >::Failure {
                error: error.clone(),
            })
        }
    }

    pub struct SimpleUnionClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleUnionImpl_Compile::Config>,
    }

    impl SimpleUnionClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleUnionImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleUnionImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dunion_dinternaldafny_dtypes::ISimpleUnionClient
        for super::r#_simple_dunion_dinternaldafny::SimpleUnionClient
    {
        fn GetUnion(
            &mut self,
            input: &::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionInput>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput>,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleUnionImpl_Compile::_default::GetUnion(&self.config(), input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetKnownValueUnion(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dunion_dinternaldafny_dtypes::GetKnownValueUnionOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dunion_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleUnionImpl_Compile::_default::GetKnownValueUnion(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
    }
}
pub mod _module {}
