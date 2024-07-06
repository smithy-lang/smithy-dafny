#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_daggregate_dinternaldafny_dtypes {
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
                        "r#_simple_daggregate_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent("
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
    pub enum GetAggregateInput {
        GetAggregateInput {
            simpleStringList: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >,
            structureList: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                        >,
                    >,
                >,
            >,
            simpleStringMap: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Map<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >,
            simpleIntegerMap: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Map<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        i32,
                    >,
                >,
            >,
            nestedStructure: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure,
                    >,
                >,
            >,
        },
    }

    impl GetAggregateInput {
        pub fn simpleStringList(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
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
        pub fn structureList(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                    >,
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
                } => structureList,
            }
        }
        pub fn simpleStringMap(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
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
            super::r#_Wrappers_Compile::Option<
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
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure>,
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

    impl ::std::fmt::Debug for GetAggregateInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetAggregateInput {
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
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.GetAggregateInput.GetAggregateInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleStringList, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(structureList, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleStringMap, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleIntegerMap, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(nestedStructure, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetAggregateInput {}

    impl ::std::hash::Hash for GetAggregateInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetAggregateInput::GetAggregateInput {
                    simpleStringList,
                    structureList,
                    simpleStringMap,
                    simpleIntegerMap,
                    nestedStructure,
                } => {
                    simpleStringList.hash(_state);
                    structureList.hash(_state);
                    simpleStringMap.hash(_state);
                    simpleIntegerMap.hash(_state);
                    nestedStructure.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetAggregateInput {
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

    impl ::std::convert::AsRef<GetAggregateInput> for &GetAggregateInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetAggregateOutput {
        GetAggregateOutput {
            simpleStringList: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >,
            structureList: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                        >,
                    >,
                >,
            >,
            simpleStringMap: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Map<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >,
            simpleIntegerMap: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Map<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        i32,
                    >,
                >,
            >,
            nestedStructure: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure,
                    >,
                >,
            >,
        },
    }

    impl GetAggregateOutput {
        pub fn simpleStringList(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
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
        pub fn structureList(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
                    >,
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
                } => structureList,
            }
        }
        pub fn simpleStringMap(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
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
            super::r#_Wrappers_Compile::Option<
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
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure>,
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

    impl ::std::fmt::Debug for GetAggregateOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetAggregateOutput {
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
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.GetAggregateOutput.GetAggregateOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleStringList, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(structureList, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleStringMap, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(simpleIntegerMap, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(nestedStructure, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetAggregateOutput {}

    impl ::std::hash::Hash for GetAggregateOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetAggregateOutput::GetAggregateOutput {
                    simpleStringList,
                    structureList,
                    simpleStringMap,
                    simpleIntegerMap,
                    nestedStructure,
                } => {
                    simpleStringList.hash(_state);
                    structureList.hash(_state);
                    simpleStringMap.hash(_state);
                    simpleIntegerMap.hash(_state);
                    nestedStructure.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetAggregateOutput {
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

    impl ::std::convert::AsRef<GetAggregateOutput> for &GetAggregateOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum NestedStructure {
        NestedStructure {
            stringStructure: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
                    >,
                >,
            >,
        },
    }

    impl NestedStructure {
        pub fn stringStructure(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>,
            >,
        > {
            match self {
                NestedStructure::NestedStructure { stringStructure } => stringStructure,
            }
        }
    }

    impl ::std::fmt::Debug for NestedStructure {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for NestedStructure {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                NestedStructure::NestedStructure { stringStructure } => {
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.NestedStructure.NestedStructure(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(stringStructure, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for NestedStructure {}

    impl ::std::hash::Hash for NestedStructure {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                NestedStructure::NestedStructure { stringStructure } => {
                    stringStructure.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for NestedStructure {
        fn default() -> NestedStructure {
            NestedStructure::NestedStructure {
                stringStructure: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<NestedStructure> for &NestedStructure {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct ISimpleAggregateClientCallHistory {}

    impl ISimpleAggregateClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleAggregateClient {
        fn GetAggregate(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        >;
        fn GetAggregateKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        >;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleAggregateConfig {
        SimpleAggregateConfig {},
    }

    impl SimpleAggregateConfig {}

    impl ::std::fmt::Debug for SimpleAggregateConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleAggregateConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleAggregateConfig::SimpleAggregateConfig {} => {
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.SimpleAggregateConfig.SimpleAggregateConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleAggregateConfig {}

    impl ::std::hash::Hash for SimpleAggregateConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleAggregateConfig::SimpleAggregateConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleAggregateConfig {
        fn default() -> SimpleAggregateConfig {
            SimpleAggregateConfig::SimpleAggregateConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleAggregateConfig> for &SimpleAggregateConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum StringStructure {
        StringStructure {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl StringStructure {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                StringStructure::StringStructure { value } => value,
            }
        }
    }

    impl ::std::fmt::Debug for StringStructure {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for StringStructure {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                StringStructure::StringStructure { value } => {
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.StringStructure.StringStructure(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for StringStructure {}

    impl ::std::hash::Hash for StringStructure {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                StringStructure::StringStructure { value } => value.hash(_state),
            }
        }
    }

    impl ::std::default::Default for StringStructure {
        fn default() -> StringStructure {
            StringStructure::StringStructure {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<StringStructure> for &StringStructure {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum StructureListElement {
        StructureListElement {
            stringValue: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
            integerValue: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>>,
        },
    }

    impl StructureListElement {
        pub fn stringValue(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
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
        pub fn integerValue(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<i32>> {
            match self {
                StructureListElement::StructureListElement {
                    stringValue,
                    integerValue,
                } => integerValue,
            }
        }
    }

    impl ::std::fmt::Debug for StructureListElement {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for StructureListElement {
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
                    write!(_formatter, "r#_simple_daggregate_dinternaldafny_dtypes.StructureListElement.StructureListElement(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(stringValue, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(integerValue, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for StructureListElement {}

    impl ::std::hash::Hash for StructureListElement {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                StructureListElement::StructureListElement {
                    stringValue,
                    integerValue,
                } => {
                    stringValue.hash(_state);
                    integerValue.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for StructureListElement {
        fn default() -> StructureListElement {
            StructureListElement::StructureListElement {
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<StructureListElement> for &StructureListElement {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
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
            ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
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
                        "r#_simple_daggregate_dinternaldafny_dtypes.Error.CollectionOfErrors("
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
                        "r#_simple_daggregate_dinternaldafny_dtypes.Error.Opaque("
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

    pub type OpaqueError = ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>;
}
pub mod r#_SimpleAggregateImpl_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn GetAggregate(
            config: &::std::rc::Rc<super::r#_SimpleAggregateImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput> = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn GetAggregateKnownValueTest(
            config: &::std::rc::Rc<super::r#_SimpleAggregateImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            super::r#_SimpleAggregateImpl_Compile::_default::ValidateInput(input);
            let mut res: ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput> = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput::GetAggregateOutput {
            simpleStringList: input.simpleStringList().clone(),
            structureList: input.structureList().clone(),
            simpleStringMap: input.simpleStringMap().clone(),
            simpleIntegerMap: input.simpleIntegerMap().clone(),
            nestedStructure: input.nestedStructure().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
        pub fn ValidateInput(
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> () {
            if !((input.simpleStringList().UnwrapOr(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>)/* <i>Coercion from ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>> to T</i> not yet implemented */)/* <i>Coercion from T to ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>></i> not yet implemented */) == ::dafny_runtime::seq![::dafny_runtime::string_utf16_of("Test")]) {
        panic!("Halt")
      };
            if !((input.simpleStringMap().UnwrapOr(&::dafny_runtime::map![]/* <i>Coercion from ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>> to T</i> not yet implemented */)/* <i>Coercion from T to ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>></i> not yet implemented */) == ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test1")) => (::dafny_runtime::string_utf16_of("Success"))]) {
        panic!("Halt")
      };
            if !((input.simpleIntegerMap().UnwrapOr(&::dafny_runtime::map![]/* <i>Coercion from ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32> to T</i> not yet implemented */)/* <i>Coercion from T to ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, i32></i> not yet implemented */) == ::dafny_runtime::map![(::dafny_runtime::string_utf16_of("Test3")) => (3)]) {
        panic!("Halt")
      };
            if !((input.structureList().UnwrapOr(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>>)/* <i>Coercion from ::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>> to T</i> not yet implemented */)/* <i>Coercion from T to ::dafny_runtime::Sequence<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement>></i> not yet implemented */) == ::dafny_runtime::seq![::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
              stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                    value: ::dafny_runtime::string_utf16_of("Test2")
                  }),
              integerValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<i32>::Some {
                    value: 2
                  })
            })]) {
        panic!("Halt")
      };
            if !((input.nestedStructure().UnwrapOr(&::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
                              stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                                            value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                                                          value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                                                                        value: ::dafny_runtime::string_utf16_of("")
                                                                      })
                                                        })
                                          })
                            })/* <i>Coercion from ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure> to T</i> not yet implemented */)/* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure></i> not yet implemented */) == ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::NestedStructure::NestedStructure {
            stringStructure: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure>>::Some {
                  value: ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
                        value: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                              value: ::dafny_runtime::string_utf16_of("Nested")
                            })
                      })
                })
          })) {
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
                    write!(_formatter, "r#_SimpleAggregateImpl_Compile.Config.Config")?;
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
pub mod r#_simple_daggregate_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleAggregateConfig(
        ) -> ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::SimpleAggregateConfig>
        {
            ::std::rc::Rc::new(super::r#_simple_daggregate_dinternaldafny_dtypes::SimpleAggregateConfig::SimpleAggregateConfig {})
        }
        pub fn SimpleAggregate(
            config: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::SimpleAggregateConfig,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut res = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Object<
                            super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut client = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<
                    super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                >,
            >::new();
            let mut _nw0: ::dafny_runtime::Object<
                super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
            > = super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient::_allocate_rcmut(
            );
            super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient::_ctor(
                &_nw0,
                &::std::rc::Rc::new(super::r#_SimpleAggregateImpl_Compile::Config::Config {}),
            );
            client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::dafny_runtime::Object<
                        super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient,
                    >,
                    ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: client.read(),
                },
            ));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(
            client: &::dafny_runtime::Object<
                dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >::Success {
                value: client.clone(),
            })
        }
        pub fn CreateFailureOfError(
            error: &::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Object<
                    dyn super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >::Failure {
                error: error.clone(),
            })
        }
    }

    pub struct SimpleAggregateClient {
        pub r#__i_config: ::std::rc::Rc<super::r#_SimpleAggregateImpl_Compile::Config>,
    }

    impl SimpleAggregateClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleAggregateImpl_Compile::Config>,
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
        pub fn config(&self) -> ::std::rc::Rc<super::r#_SimpleAggregateImpl_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_daggregate_dinternaldafny_dtypes::ISimpleAggregateClient
        for super::r#_simple_daggregate_dinternaldafny::SimpleAggregateClient
    {
        fn GetAggregate(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleAggregateImpl_Compile::_default::GetAggregate(
                    &self.config(),
                    input,
                ),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn GetAggregateKnownValueTest(
            &mut self,
            input: &::std::rc::Rc<
                super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                >,
                ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            super::r#_simple_daggregate_dinternaldafny_dtypes::GetAggregateOutput,
                        >,
                        ::std::rc::Rc<super::r#_simple_daggregate_dinternaldafny_dtypes::Error>,
                    >,
                >,
            >::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                super::r#_SimpleAggregateImpl_Compile::_default::GetAggregateKnownValueTest(
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
