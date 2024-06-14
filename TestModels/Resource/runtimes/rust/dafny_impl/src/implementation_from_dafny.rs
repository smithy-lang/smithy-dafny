#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dresources_dinternaldafny_dtypes {
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
                        "r#_simple_dresources_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent("
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
    pub enum GetResourceDataInput {
        GetResourceDataInput {
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

    impl GetResourceDataInput {
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
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
        pub fn booleanValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
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
            super::r#_Wrappers_Compile::Option<
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
        pub fn integerValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
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
        pub fn longValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>> {
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

    impl ::std::fmt::Debug for GetResourceDataInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetResourceDataInput {
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
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.GetResourceDataInput.GetResourceDataInput(")?;
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

    impl Eq for GetResourceDataInput {}

    impl ::std::hash::Hash for GetResourceDataInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetResourceDataInput::GetResourceDataInput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    blobValue.hash(_state);
                    booleanValue.hash(_state);
                    stringValue.hash(_state);
                    integerValue.hash(_state);
                    longValue.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetResourceDataInput {
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

    impl ::std::convert::AsRef<GetResourceDataInput> for &GetResourceDataInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetResourceDataOutput {
        GetResourceDataOutput {
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

    impl GetResourceDataOutput {
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
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
        pub fn booleanValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
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
            super::r#_Wrappers_Compile::Option<
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
        pub fn integerValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
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
        pub fn longValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i64>> {
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

    impl ::std::fmt::Debug for GetResourceDataOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetResourceDataOutput {
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
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.GetResourceDataOutput.GetResourceDataOutput(")?;
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

    impl Eq for GetResourceDataOutput {}

    impl ::std::hash::Hash for GetResourceDataOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetResourceDataOutput::GetResourceDataOutput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    blobValue.hash(_state);
                    booleanValue.hash(_state);
                    stringValue.hash(_state);
                    integerValue.hash(_state);
                    longValue.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetResourceDataOutput {
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

    impl ::std::convert::AsRef<GetResourceDataOutput> for &GetResourceDataOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetResourcesInput {
        GetResourcesInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetResourcesInput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetResourcesInput::GetResourcesInput { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for GetResourcesInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetResourcesInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetResourcesInput::GetResourcesInput { value } => {
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.GetResourcesInput.GetResourcesInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetResourcesInput {}

    impl ::std::hash::Hash for GetResourcesInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetResourcesInput::GetResourcesInput { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for GetResourcesInput {
        fn default() -> GetResourcesInput {
            GetResourcesInput::GetResourcesInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetResourcesInput> for &GetResourcesInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetResourcesOutput {
        GetResourcesOutput {
            output: ::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
            >,
        },
    }

    impl GetResourcesOutput {
        pub fn output(
            &self,
        ) -> &::dafny_runtime::Object<
            dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource,
        > {
            match self {
                GetResourcesOutput::GetResourcesOutput { output } => output,
            }
        }
    }

    impl ::std::fmt::Debug for GetResourcesOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetResourcesOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetResourcesOutput::GetResourcesOutput { output } => {
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.GetResourcesOutput.GetResourcesOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetResourcesOutput {}

    impl ::std::hash::Hash for GetResourcesOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetResourcesOutput::GetResourcesOutput { output } => output.hash(_state),
            }
        }
    }

    // the trait `Default` is not implemented for `Object<(dyn ISimpleResource + 'static)>`
    // impl ::std::default::Default for GetResourcesOutput {
    //     fn default() -> GetResourcesOutput {
    //         GetResourcesOutput::GetResourcesOutput {
    //             output: ::std::default::Default::default(),
    //         }
    //     }
    // }

    impl ::std::convert::AsRef<GetResourcesOutput> for &GetResourcesOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleResourceCallHistory {}

    impl ISimpleResourceCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleResource {
        fn GetResourceData(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                self.r#_GetResourceData_k(input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn r#_GetResourceData_k(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    pub struct ISimpleResourcesClientCallHistory {}

    impl ISimpleResourcesClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleResourcesClient {
        fn GetResources(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
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
        pub fn name(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                SimpleResourcesConfig::SimpleResourcesConfig { name } => name,
            }
        }
    }

    impl ::std::fmt::Debug for SimpleResourcesConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleResourcesConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleResourcesConfig::SimpleResourcesConfig { name } => {
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.SimpleResourcesConfig.SimpleResourcesConfig(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(name, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleResourcesConfig {}

    impl ::std::hash::Hash for SimpleResourcesConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleResourcesConfig::SimpleResourcesConfig { name } => name.hash(_state),
            }
        }
    }

    impl ::std::default::Default for SimpleResourcesConfig {
        fn default() -> SimpleResourcesConfig {
            SimpleResourcesConfig::SimpleResourcesConfig {
                name: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<SimpleResourcesConfig> for &SimpleResourcesConfig {
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
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        Opaque {
            obj: ::dafny_runtime::Object<dyn::std::any::Any>,
        },
    }

    impl Error {
        pub fn message(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                Error::SimpleResourcesException { message } => message,
                Error::CollectionOfErrors { list, message } => message,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn list(
            &self,
        ) -> &::dafny_runtime::Sequence<
            ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
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
                Error::SimpleResourcesException { message } => {
                    write!(_formatter, "r#_simple_dresources_dinternaldafny_dtypes.Error.SimpleResourcesException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::CollectionOfErrors { list, message } => {
                    write!(
                        _formatter,
                        "r#_simple_dresources_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_dresources_dinternaldafny_dtypes.Error.Opaque("
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
                Error::SimpleResourcesException { message } => message.hash(_state),
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
            Error::SimpleResourcesException {
                message: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Error> for &Error {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type OpaqueError = ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleResource_Compile {
    pub struct SimpleResource {
        pub r#__i_value: ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        >,
        pub r#__i_name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
    }

    impl SimpleResource {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetResourceData(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource::GetResourceData(
                    self,
                    input,
                ),
            );
            _out1.read()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            value: &::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            name: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> () {
            let mut _set__i_value: bool = false;
            let mut _set__i_name: bool = false;
            ::dafny_runtime::update_field_uninit_rcmut!(
                this.clone(),
                r#__i_value,
                _set__i_value,
                value.clone()
            );
            ::dafny_runtime::update_field_uninit_rcmut!(
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
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            self.r#__i_value.clone()
        }
        pub fn name(&self) -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            self.r#__i_name.clone()
        }
    }

    impl super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource
        for super::r#_SimpleResource_Compile::SimpleResource
    {
        fn r#_GetResourceData_k(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut rtnString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = (if matches!(
                input.stringValue().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                self.name()
                    .concat(&::dafny_runtime::string_utf16_of(" "))
                    .concat(input.stringValue().value())
            } else {
                self.name()
            });
            rtnString = (if matches!(
                input.stringValue().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                self.name()
                    .concat(&::dafny_runtime::string_utf16_of(" "))
                    .concat(input.stringValue().value())
            } else {
                self.name()
            });
            let mut rtn: ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput> = ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput::GetResourceDataOutput {
            blobValue: input.blobValue().clone(),
            booleanValue: input.booleanValue().clone(),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: rtnString.clone()
                }),
            integerValue: input.integerValue().clone(),
            longValue: input.longValue().clone()
          });
            rtn = ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput::GetResourceDataOutput {
            blobValue: input.blobValue().clone(),
            booleanValue: input.booleanValue().clone(),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: rtnString.clone()
                }),
            integerValue: input.integerValue().clone(),
            longValue: input.longValue().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dresources_dinternaldafny_dtypes::GetResourceDataOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: rtn.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
    }
}
pub mod r#_SimpleResourcesOperations_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn r#_ValidInternalConfig_q(
            config: &::std::rc::Rc<super::r#_SimpleResourcesOperations_Compile::Config>,
        ) -> bool {
            true && ::dafny_runtime::int!(0) < config.name().cardinality()
        }
        pub fn GetResources(
            config: &::std::rc::Rc<super::r#_SimpleResourcesOperations_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<super::r#_SimpleResource_Compile::SimpleResource>,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<
                super::r#_SimpleResource_Compile::SimpleResource,
            > = super::r#_SimpleResource_Compile::SimpleResource::_allocate_rcmut();
            super::r#_SimpleResource_Compile::SimpleResource::_ctor(
                &_nw0,
                input.value(),
                config.name(),
            );
            resource = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            let mut result: ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput> = ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput::GetResourcesOutput {
            output: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource>>::upcast_to(resource.read())
          });
            result = ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput::GetResourcesOutput {
            output: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResource>>::upcast_to(resource.read())
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: result.clone(),
                },
            ));
            return output.read();
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
                Config::Config { name } => {
                    write!(
                        _formatter,
                        "r#_SimpleResourcesOperations_Compile.Config.Config("
                    )?;
                    ::dafny_runtime::DafnyPrint::fmt_print(name, _formatter, false)?;
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
                Config::Config { name } => name.hash(_state),
            }
        }
    }

    impl ::std::default::Default for Config {
        fn default() -> Config {
            Config::Config {
                name: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Config> for &Config {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod r#_simple_dresources_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleResourcesConfig(
        ) -> ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig::SimpleResourcesConfig {
          name: ::dafny_runtime::string_utf16_of("default")
        })
        }
        pub fn SimpleResources(
            config: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut internalConfig: ::std::rc::Rc<
                super::r#_SimpleResourcesOperations_Compile::Config,
            > = ::std::rc::Rc::new(
                super::r#_SimpleResourcesOperations_Compile::Config::Config {
                    name: config.name().clone(),
                },
            );
            internalConfig = ::std::rc::Rc::new(
                super::r#_SimpleResourcesOperations_Compile::Config::Config {
                    name: config.name().clone(),
                },
            );
            if super::r#_SimpleResourcesOperations_Compile::_default::r#_ValidInternalConfig_q(
                &internalConfig,
            ) {
                let mut client = ::dafny_runtime::MaybePlacebo::<
                    ::dafny_runtime::Object<
                        super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                    >,
                >::new();
                let mut _nw1: ::dafny_runtime::Object<super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient> = super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient::_allocate_rcmut();
                super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient::_ctor(
                    &_nw1,
                    &internalConfig,
                );
                client = ::dafny_runtime::MaybePlacebo::from(_nw1.clone());
                res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                    super::r#_Wrappers_Compile::Result::<
                        ::dafny_runtime::Object<
                            super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >::Success {
                        value: client.read(),
                    },
                ));
                return res.read();
            } else {
                res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient>, ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>>::Failure {
                error: ::std::rc::Rc::new(super::r#_simple_dresources_dinternaldafny_dtypes::Error::SimpleResourcesException {
                      message: ::dafny_runtime::string_utf16_of("Length of name must be greater than 0")
                    })
              }));
                return res.read();
            };
            return res.read();
        }
        pub fn CreateSuccessOfClient(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >::Success {
                value: client.clone(),
            })
        }
        pub fn CreateFailureOfError(
            error: &::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >::Failure {
                error: error.clone(),
            })
        }
    }

    pub struct SimpleResourcesClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleResourcesOperations_Compile::Config>,
    }

    impl SimpleResourcesClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleResourcesOperations_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleResourcesOperations_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dresources_dinternaldafny_dtypes::ISimpleResourcesClient
        for super::r#_simple_dresources_dinternaldafny::SimpleResourcesClient
    {
        fn GetResources(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_dresources_dinternaldafny_dtypes::GetResourcesOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_dresources_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleResourcesOperations_Compile::_default::GetResources(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
    }
}
pub mod _module {}
