#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dconstructor_dinternaldafny_dtypes {
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
                        "simple.constructor.internaldafny.types.DafnyCallEvent.DafnyCallEvent("
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
                    ::std::hash::Hash::hash(input, _state);
                    ::std::hash::Hash::hash(output, _state)
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
    pub enum GetConstructorInput {
        GetConstructorInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetConstructorInput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetConstructorInput::GetConstructorInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetConstructorInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetConstructorInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetConstructorInput::GetConstructorInput { value } => {
                    write!(_formatter, "simple.constructor.internaldafny.types.GetConstructorInput.GetConstructorInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetConstructorInput {}

    impl ::std::hash::Hash for GetConstructorInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetConstructorInput::GetConstructorInput { value } => {
                    ::std::hash::Hash::hash(value, _state)
                }
            }
        }
    }

    impl ::std::default::Default for GetConstructorInput {
        fn default() -> GetConstructorInput {
            GetConstructorInput::GetConstructorInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetConstructorInput> for &GetConstructorInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetConstructorOutput {
        GetConstructorOutput {
            internalConfigString: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            blobValue:
                ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>,
            booleanValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>,
            stringValue: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            integerValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>>,
            longValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>>,
        },
    }

    impl GetConstructorOutput {
        pub fn internalConfigString(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => internalConfigString,
            }
        }
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => blobValue,
            }
        }
        pub fn booleanValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
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
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => stringValue,
            }
        }
        pub fn integerValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => integerValue,
            }
        }
        pub fn longValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>> {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => longValue,
            }
        }
    }

    impl ::std::fmt::Debug for GetConstructorOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetConstructorOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    write!(_formatter, "simple.constructor.internaldafny.types.GetConstructorOutput.GetConstructorOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        internalConfigString,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(blobValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(booleanValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(stringValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(integerValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(longValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetConstructorOutput {}

    impl ::std::hash::Hash for GetConstructorOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetConstructorOutput::GetConstructorOutput {
                    internalConfigString,
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    ::std::hash::Hash::hash(internalConfigString, _state);
                    ::std::hash::Hash::hash(blobValue, _state);
                    ::std::hash::Hash::hash(booleanValue, _state);
                    ::std::hash::Hash::hash(stringValue, _state);
                    ::std::hash::Hash::hash(integerValue, _state);
                    ::std::hash::Hash::hash(longValue, _state)
                }
            }
        }
    }

    impl ::std::default::Default for GetConstructorOutput {
        fn default() -> GetConstructorOutput {
            GetConstructorOutput::GetConstructorOutput {
                internalConfigString: ::std::default::Default::default(),
                blobValue: ::std::default::Default::default(),
                booleanValue: ::std::default::Default::default(),
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
                longValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetConstructorOutput> for &GetConstructorOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleConstructorClientCallHistory {}

    impl ISimpleConstructorClientCallHistory {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClientCallHistory
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    pub trait ISimpleConstructorClient:
        ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
    {
        fn GetConstructor(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleConstructorConfig {
        SimpleConstructorConfig {
            blobValue:
                ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>,
            booleanValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>,
            stringValue: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            integerValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>>,
            longValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>>,
        },
    }

    impl SimpleConstructorConfig {
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => blobValue,
            }
        }
        pub fn booleanValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
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
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => stringValue,
            }
        }
        pub fn integerValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => integerValue,
            }
        }
        pub fn longValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>> {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => longValue,
            }
        }
    }

    impl ::std::fmt::Debug for SimpleConstructorConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleConstructorConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    write!(_formatter, "simple.constructor.internaldafny.types.SimpleConstructorConfig.SimpleConstructorConfig(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(blobValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(booleanValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(stringValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(integerValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(longValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleConstructorConfig {}

    impl ::std::hash::Hash for SimpleConstructorConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleConstructorConfig::SimpleConstructorConfig {
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

    impl ::std::default::Default for SimpleConstructorConfig {
        fn default() -> SimpleConstructorConfig {
            SimpleConstructorConfig::SimpleConstructorConfig {
                blobValue: ::std::default::Default::default(),
                booleanValue: ::std::default::Default::default(),
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
                longValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<SimpleConstructorConfig> for &SimpleConstructorConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
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
                        "simple.constructor.internaldafny.types.Error.CollectionOfErrors("
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
                        "simple.constructor.internaldafny.types.Error.Opaque("
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
                    ::std::hash::Hash::hash(list, _state);
                    ::std::hash::Hash::hash(message, _state)
                }
                Error::Opaque { obj } => ::std::hash::Hash::hash(obj, _state),
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

    pub type OpaqueError =
        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleConstructorImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn GetConstructor(
            config: &::std::rc::Rc<super::r#_SimpleConstructorImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput> = ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput::GetConstructorOutput {
            internalConfigString: input.value().clone(),
            blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                  value: config.blobValue().clone()
                }),
            booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                  value: config.booleanValue().clone()
                }),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: config.stringValue().clone()
                }),
            integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                  value: config.integerValue().clone()
                }),
            longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                  value: config.longValue().clone()
                })
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_SimpleConstructorImpl_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    #[derive(PartialEq, Clone)]
    pub enum Config {
        Config {
            blobValue: ::dafny_runtime::Sequence<u8>,
            booleanValue: bool,
            stringValue: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            integerValue: i32,
            longValue: i64,
        },
    }

    impl Config {
        pub fn blobValue(&self) -> &::dafny_runtime::Sequence<u8> {
            match self {
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => blobValue,
            }
        }
        pub fn booleanValue(&self) -> &bool {
            match self {
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => booleanValue,
            }
        }
        pub fn stringValue(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => stringValue,
            }
        }
        pub fn integerValue(&self) -> &i32 {
            match self {
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => integerValue,
            }
        }
        pub fn longValue(&self) -> &i64 {
            match self {
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => longValue,
            }
        }
    }

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
                Config::Config {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    write!(_formatter, "SimpleConstructorImpl_Compile.Config.Config(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(blobValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(booleanValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(stringValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(integerValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(longValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Config {}

    impl ::std::hash::Hash for Config {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Config::Config {
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

    impl ::std::default::Default for Config {
        fn default() -> Config {
            Config::Config {
                blobValue: ::std::default::Default::default(),
                booleanValue: ::std::default::Default::default(),
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
                longValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Config> for &Config {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod r#_simple_dconstructor_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn DefaultSimpleConstructorConfig() -> ::std::rc::Rc<
            super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig,
        > {
            ::std::rc::Rc::new(super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig::SimpleConstructorConfig {
          blobValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<u8>>::Some {
                value: ::dafny_runtime::seq![0]
              }),
          booleanValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
                value: false
              }),
          stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                value: ::dafny_runtime::string_utf16_of("")
              }),
          integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                value: 0
              }),
          longValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i64>::Some {
                value: 0
              })
        })
        }
        pub fn SimpleConstructor(
            config: &::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                >,
                ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut configToAssign: ::std::rc::Rc<super::r#_SimpleConstructorImpl_Compile::Config> =
                ::std::rc::Rc::new(super::r#_SimpleConstructorImpl_Compile::Config::Config {
                    blobValue: config.blobValue().UnwrapOr(&::dafny_runtime::seq![0]),
                    booleanValue: config.booleanValue().UnwrapOr(&true),
                    stringValue: config
                        .stringValue()
                        .UnwrapOr(&::dafny_runtime::string_utf16_of("")),
                    integerValue: config.integerValue().UnwrapOr(&0),
                    longValue: config.longValue().UnwrapOr(&0),
                });
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient> = super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient::_allocate_object();
            super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient::_ctor(
                &_nw0,
                &configToAssign,
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dconstructor_dinternaldafny::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    pub struct SimpleConstructorClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleConstructorImpl_Compile::Config>,
    }

    impl SimpleConstructorClient {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<
                super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient,
            >,
            config: &::std::rc::Rc<super::r#_SimpleConstructorImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleConstructorImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    impl super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient
        for super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient
    {
        fn GetConstructor(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::GetConstructorOutput>, ::std::rc::Rc<super::r#_simple_dconstructor_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleConstructorImpl_Compile::_default::GetConstructor(
                    &self.config().clone(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
    }

    impl
        ::dafny_runtime::UpcastObject<
            dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient,
        > for super::r#_simple_dconstructor_dinternaldafny::SimpleConstructorClient
    {
        ::dafny_runtime::UpcastObjectFn!(dyn super::r#_simple_dconstructor_dinternaldafny_dtypes::ISimpleConstructorClient);
    }
}
pub mod _module {}
