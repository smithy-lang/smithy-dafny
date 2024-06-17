#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dextendable_dresources_dinternaldafny_dtypes {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn IsValid_Name(
            x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
        }
    }

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
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.DafnyCallEvent.DafnyCallEvent(")?;
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
    pub enum CreateExtendableResourceInput {
        CreateExtendableResourceInput {
            name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
    }

    impl CreateExtendableResourceInput {
        pub fn name(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                CreateExtendableResourceInput::CreateExtendableResourceInput { name } => name,
            }
        }
    }

    impl ::std::fmt::Debug for CreateExtendableResourceInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for CreateExtendableResourceInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                CreateExtendableResourceInput::CreateExtendableResourceInput { name } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.CreateExtendableResourceInput.CreateExtendableResourceInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(name, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for CreateExtendableResourceInput {}

    impl ::std::hash::Hash for CreateExtendableResourceInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                CreateExtendableResourceInput::CreateExtendableResourceInput { name } => {
                    name.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for CreateExtendableResourceInput {
        fn default() -> CreateExtendableResourceInput {
            CreateExtendableResourceInput::CreateExtendableResourceInput {
                name: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<CreateExtendableResourceInput> for &CreateExtendableResourceInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum CreateExtendableResourceOutput {
        CreateExtendableResourceOutput {
      resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>
    }
  }

    impl CreateExtendableResourceOutput {
        pub fn resource(
            &self,
        ) -> &::dafny_runtime::Object<
            dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource,
        > {
            match self {
                CreateExtendableResourceOutput::CreateExtendableResourceOutput { resource } => {
                    resource
                }
            }
        }
    }

    impl ::std::fmt::Debug for CreateExtendableResourceOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for CreateExtendableResourceOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                CreateExtendableResourceOutput::CreateExtendableResourceOutput { resource } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.CreateExtendableResourceOutput.CreateExtendableResourceOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(resource, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for CreateExtendableResourceOutput {}

    impl ::std::hash::Hash for CreateExtendableResourceOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                CreateExtendableResourceOutput::CreateExtendableResourceOutput { resource } => {
                    resource.hash(_state)
                }
            }
        }
    }

    //  the trait `Default` is not implemented for `Object<(dyn IExtendableResource + 'static)>`
    // impl ::std::default::Default for CreateExtendableResourceOutput {
    //     fn default() -> CreateExtendableResourceOutput {
    //         CreateExtendableResourceOutput::CreateExtendableResourceOutput {
    //             resource: ::std::default::Default::default(),
    //         }
    //     }
    // }

    impl ::std::convert::AsRef<CreateExtendableResourceOutput> for &CreateExtendableResourceOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct IExtendableResourceCallHistory {}

    impl IExtendableResourceCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait IExtendableResource {
        fn GetExtendableResourceData(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(
                self.r#_GetExtendableResourceData_k(input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            return output.read();
        }
        fn r#_GetExtendableResourceData_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn AlwaysMultipleErrors(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(
                self.r#_AlwaysMultipleErrors_k(input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            return output.read();
        }
        fn r#_AlwaysMultipleErrors_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn AlwaysModeledError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(
                self.r#_AlwaysModeledError_k(input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            return output.read();
        }
        fn r#_AlwaysModeledError_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn AlwaysOpaqueError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(
                self.r#_AlwaysOpaqueError_k(input),
            );
            output = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            return output.read();
        }
        fn r#_AlwaysOpaqueError_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
    }

    #[derive(PartialEq, Clone)]
    pub enum GetExtendableResourceDataInput {
        GetExtendableResourceDataInput {
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

    impl GetExtendableResourceDataInput {
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
            match self {
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
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
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
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
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
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
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
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
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => longValue,
            }
        }
    }

    impl ::std::fmt::Debug for GetExtendableResourceDataInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetExtendableResourceDataInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.GetExtendableResourceDataInput.GetExtendableResourceDataInput(")?;
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

    impl Eq for GetExtendableResourceDataInput {}

    impl ::std::hash::Hash for GetExtendableResourceDataInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetExtendableResourceDataInput::GetExtendableResourceDataInput {
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

    impl ::std::default::Default for GetExtendableResourceDataInput {
        fn default() -> GetExtendableResourceDataInput {
            GetExtendableResourceDataInput::GetExtendableResourceDataInput {
                blobValue: ::std::default::Default::default(),
                booleanValue: ::std::default::Default::default(),
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
                longValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetExtendableResourceDataInput> for &GetExtendableResourceDataInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetExtendableResourceDataOutput {
        GetExtendableResourceDataOutput {
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

    impl GetExtendableResourceDataOutput {
        pub fn blobValue(
            &self,
        ) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>
        {
            match self {
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
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
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
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
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
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
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
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
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => longValue,
            }
        }
    }

    impl ::std::fmt::Debug for GetExtendableResourceDataOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetExtendableResourceDataOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
                    blobValue,
                    booleanValue,
                    stringValue,
                    integerValue,
                    longValue,
                } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.GetExtendableResourceDataOutput.GetExtendableResourceDataOutput(")?;
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

    impl Eq for GetExtendableResourceDataOutput {}

    impl ::std::hash::Hash for GetExtendableResourceDataOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
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

    impl ::std::default::Default for GetExtendableResourceDataOutput {
        fn default() -> GetExtendableResourceDataOutput {
            GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
                blobValue: ::std::default::Default::default(),
                booleanValue: ::std::default::Default::default(),
                stringValue: ::std::default::Default::default(),
                integerValue: ::std::default::Default::default(),
                longValue: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetExtendableResourceDataOutput> for &GetExtendableResourceDataOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetExtendableResourceErrorsInput {
        GetExtendableResourceErrorsInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetExtendableResourceErrorsInput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetExtendableResourceErrorsInput::GetExtendableResourceErrorsInput { value } => {
                    value
                }
            }
        }
    }

    impl ::std::fmt::Debug for GetExtendableResourceErrorsInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetExtendableResourceErrorsInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetExtendableResourceErrorsInput::GetExtendableResourceErrorsInput { value } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.GetExtendableResourceErrorsInput.GetExtendableResourceErrorsInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetExtendableResourceErrorsInput {}

    impl ::std::hash::Hash for GetExtendableResourceErrorsInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetExtendableResourceErrorsInput::GetExtendableResourceErrorsInput { value } => {
                    value.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetExtendableResourceErrorsInput {
        fn default() -> GetExtendableResourceErrorsInput {
            GetExtendableResourceErrorsInput::GetExtendableResourceErrorsInput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetExtendableResourceErrorsInput> for &GetExtendableResourceErrorsInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetExtendableResourceErrorsOutput {
        GetExtendableResourceErrorsOutput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
    }

    impl GetExtendableResourceErrorsOutput {
        pub fn value(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetExtendableResourceErrorsOutput::GetExtendableResourceErrorsOutput { value } => {
                    value
                }
            }
        }
    }

    impl ::std::fmt::Debug for GetExtendableResourceErrorsOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetExtendableResourceErrorsOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetExtendableResourceErrorsOutput::GetExtendableResourceErrorsOutput { value } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.GetExtendableResourceErrorsOutput.GetExtendableResourceErrorsOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetExtendableResourceErrorsOutput {}

    impl ::std::hash::Hash for GetExtendableResourceErrorsOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetExtendableResourceErrorsOutput::GetExtendableResourceErrorsOutput { value } => {
                    value.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetExtendableResourceErrorsOutput {
        fn default() -> GetExtendableResourceErrorsOutput {
            GetExtendableResourceErrorsOutput::GetExtendableResourceErrorsOutput {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetExtendableResourceErrorsOutput>
        for &GetExtendableResourceErrorsOutput
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type Name = ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

    pub struct ISimpleExtendableResourcesClientCallHistory {}

    impl ISimpleExtendableResourcesClientCallHistory {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
    }

    pub trait ISimpleExtendableResourcesClient {
        fn CreateExtendableResource(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn UseExtendableResource(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn UseExtendableResourceAlwaysModeledError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn UseExtendableResourceAlwaysMultipleErrors(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
        fn UseExtendableResourceAlwaysOpaqueError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>;
    }

    #[derive(PartialEq, Clone)]
    pub enum SimpleExtendableResourcesConfig {
        SimpleExtendableResourcesConfig {},
    }

    impl SimpleExtendableResourcesConfig {}

    impl ::std::fmt::Debug for SimpleExtendableResourcesConfig {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleExtendableResourcesConfig {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SimpleExtendableResourcesConfig::SimpleExtendableResourcesConfig {} => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.SimpleExtendableResourcesConfig.SimpleExtendableResourcesConfig")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SimpleExtendableResourcesConfig {}

    impl ::std::hash::Hash for SimpleExtendableResourcesConfig {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SimpleExtendableResourcesConfig::SimpleExtendableResourcesConfig {} => {}
            }
        }
    }

    impl ::std::default::Default for SimpleExtendableResourcesConfig {
        fn default() -> SimpleExtendableResourcesConfig {
            SimpleExtendableResourcesConfig::SimpleExtendableResourcesConfig {}
        }
    }

    impl ::std::convert::AsRef<SimpleExtendableResourcesConfig> for &SimpleExtendableResourcesConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum UseExtendableResourceErrorsInput {
        UseExtendableResourceErrorsInput {
      resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>,
      input: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>
    }
  }

    impl UseExtendableResourceErrorsInput {
        pub fn resource(
            &self,
        ) -> &::dafny_runtime::Object<
            dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource,
        > {
            match self {
                UseExtendableResourceErrorsInput::UseExtendableResourceErrorsInput {
                    resource,
                    input,
                } => resource,
            }
        }
        pub fn input(&self) -> &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>{
            match self {
                UseExtendableResourceErrorsInput::UseExtendableResourceErrorsInput {
                    resource,
                    input,
                } => input,
            }
        }
    }

    impl ::std::fmt::Debug for UseExtendableResourceErrorsInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for UseExtendableResourceErrorsInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                UseExtendableResourceErrorsInput::UseExtendableResourceErrorsInput {
                    resource,
                    input,
                } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.UseExtendableResourceErrorsInput.UseExtendableResourceErrorsInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(resource, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for UseExtendableResourceErrorsInput {}

    impl ::std::hash::Hash for UseExtendableResourceErrorsInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                UseExtendableResourceErrorsInput::UseExtendableResourceErrorsInput {
                    resource,
                    input,
                } => {
                    resource.hash(_state);
                    input.hash(_state)
                }
            }
        }
    }
    // the trait `Default` is not implemented for `Object<(dyn IExtendableResource + 'static)>`
    // impl ::std::default::Default for UseExtendableResourceErrorsInput {
    //     fn default() -> UseExtendableResourceErrorsInput {
    //         UseExtendableResourceErrorsInput::UseExtendableResourceErrorsInput {
    //             resource: ::std::default::Default::default(),
    //             input: ::std::default::Default::default(),
    //         }
    //     }
    // }

    impl ::std::convert::AsRef<UseExtendableResourceErrorsInput> for &UseExtendableResourceErrorsInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum UseExtendableResourceInput {
        UseExtendableResourceInput {
      resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>,
      input: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>
    }
  }

    impl UseExtendableResourceInput {
        pub fn resource(
            &self,
        ) -> &::dafny_runtime::Object<
            dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource,
        > {
            match self {
                UseExtendableResourceInput::UseExtendableResourceInput { resource, input } => {
                    resource
                }
            }
        }
        pub fn input(&self) -> &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>{
            match self {
                UseExtendableResourceInput::UseExtendableResourceInput { resource, input } => input,
            }
        }
    }

    impl ::std::fmt::Debug for UseExtendableResourceInput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for UseExtendableResourceInput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                UseExtendableResourceInput::UseExtendableResourceInput { resource, input } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.UseExtendableResourceInput.UseExtendableResourceInput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(resource, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for UseExtendableResourceInput {}

    impl ::std::hash::Hash for UseExtendableResourceInput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                UseExtendableResourceInput::UseExtendableResourceInput { resource, input } => {
                    resource.hash(_state);
                    input.hash(_state)
                }
            }
        }
    }
    // the trait `Default` is not implemented for `Object<(dyn IExtendableResource + 'static)>`
    // impl ::std::default::Default for UseExtendableResourceInput {
    //     fn default() -> UseExtendableResourceInput {
    //         UseExtendableResourceInput::UseExtendableResourceInput {
    //             resource: ::std::default::Default::default(),
    //             input: ::std::default::Default::default(),
    //         }
    //     }
    // }

    impl ::std::convert::AsRef<UseExtendableResourceInput> for &UseExtendableResourceInput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum UseExtendableResourceOutput {
        UseExtendableResourceOutput {
      output: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>
    }
  }

    impl UseExtendableResourceOutput {
        pub fn output(&self) -> &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>{
            match self {
                UseExtendableResourceOutput::UseExtendableResourceOutput { output } => output,
            }
        }
    }

    impl ::std::fmt::Debug for UseExtendableResourceOutput {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for UseExtendableResourceOutput {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                UseExtendableResourceOutput::UseExtendableResourceOutput { output } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.UseExtendableResourceOutput.UseExtendableResourceOutput(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for UseExtendableResourceOutput {}

    impl ::std::hash::Hash for UseExtendableResourceOutput {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                UseExtendableResourceOutput::UseExtendableResourceOutput { output } => {
                    output.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for UseExtendableResourceOutput {
        fn default() -> UseExtendableResourceOutput {
            UseExtendableResourceOutput::UseExtendableResourceOutput {
                output: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<UseExtendableResourceOutput> for &UseExtendableResourceOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        SimpleExtendableResourcesException {
            message: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        },
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<
                ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>,
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
                Error::SimpleExtendableResourcesException { message } => message,
                Error::CollectionOfErrors { list, message } => message,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn list(
            &self,
        ) -> &::dafny_runtime::Sequence<
            ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>,
        > {
            match self {
                Error::SimpleExtendableResourcesException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::CollectionOfErrors { list, message } => list,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
            match self {
                Error::SimpleExtendableResourcesException { message } => {
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
                Error::SimpleExtendableResourcesException { message } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.Error.SimpleExtendableResourcesException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::CollectionOfErrors { list, message } => {
                    write!(_formatter, "r#_simple_dextendable_dresources_dinternaldafny_dtypes.Error.CollectionOfErrors(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::Opaque { obj } => {
                    write!(
                        _formatter,
                        "r#_simple_dextendable_dresources_dinternaldafny_dtypes.Error.Opaque("
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
                Error::SimpleExtendableResourcesException { message } => message.hash(_state),
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
            Error::SimpleExtendableResourcesException {
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
        ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>;
}
pub mod r#_ExtendableResource_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DEFAULT_RESOURCE_NAME() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
        {
            ::dafny_runtime::string_utf16_of("dafny-default")
        }
    }

    pub struct OpaqueMessage {}

    impl OpaqueMessage {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(this: &::dafny_runtime::Object<Self>) -> () {
            return ();
        }
        pub fn message(&self) -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of(
                "Hard Coded Opaque Message that will not survive translation.",
            )
        }
    }

    pub struct ExtendableResource {
        pub r#__i_name: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
    }

    impl ExtendableResource {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn AlwaysModeledError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource::AlwaysModeledError(self, input));
            _out4.read()
        }
        pub fn AlwaysMultipleErrors(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource::AlwaysMultipleErrors(self, input));
            _out5.read()
        }
        pub fn AlwaysOpaqueError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut _out6 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out6 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource::AlwaysOpaqueError(self, input));
            _out6.read()
        }
        pub fn GetExtendableResourceData(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut _out7 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out7 = ::dafny_runtime::MaybePlacebo::from(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource::GetExtendableResourceData(self, input));
            _out7.read()
        }
        pub fn _ctor(this: &::dafny_runtime::Object<Self>) -> () {
            let mut _set__i_name: bool = false;
            ::dafny_runtime::update_field_uninit_rcmut!(
                this.clone(),
                r#__i_name,
                _set__i_name,
                super::r#_ExtendableResource_Compile::_default::DEFAULT_RESOURCE_NAME()
            );
            return ();
        }
        pub fn OfName(
            &mut self,
            name: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> () {
            let mut _set__i_name: bool = false;
            self.r#__i_name = name.clone();
            ::dafny_runtime::update_field_if_uninit!(self, r#__i_name, _set__i_name, <::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> as std::default::Default>::default());
            return ();
        }
        pub fn name(&self) -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            self.r#__i_name.clone()
        }
    }

    impl super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource
        for super::r#_ExtendableResource_Compile::ExtendableResource
    {
        fn r#_AlwaysMultipleErrors_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut nestedError: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error> = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::SimpleExtendableResourcesException {
            message: ::dafny_runtime::string_utf16_of("Hard Coded Modeled Exception in Collection")
          });
            nestedError = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::SimpleExtendableResourcesException {
            message: ::dafny_runtime::string_utf16_of("Hard Coded Modeled Exception in Collection")
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Failure {
              error: ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::CollectionOfErrors {
                    list: ::dafny_runtime::seq![nestedError.clone()],
                    message: ::dafny_runtime::string_utf16_of("Something")
                  })
            }));
            return output.read();
            return output.read();
        }
        fn r#_GetExtendableResourceData_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut rtnString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = (if matches!(
                input.stringValue().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                input
                    .stringValue()
                    .value()
                    .concat(&::dafny_runtime::string_utf16_of(" "))
                    .concat(&self.name())
            } else {
                self.name()
            });
            rtnString = (if matches!(
                input.stringValue().as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                input
                    .stringValue()
                    .value()
                    .concat(&::dafny_runtime::string_utf16_of(" "))
                    .concat(&self.name())
            } else {
                self.name()
            });
            let mut rtn: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput> = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
            blobValue: input.blobValue().clone(),
            booleanValue: input.booleanValue().clone(),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: rtnString.clone()
                }),
            integerValue: input.integerValue().clone(),
            longValue: input.longValue().clone()
          });
            rtn = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput::GetExtendableResourceDataOutput {
            blobValue: input.blobValue().clone(),
            booleanValue: input.booleanValue().clone(),
            stringValue: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: rtnString.clone()
                }),
            integerValue: input.integerValue().clone(),
            longValue: input.longValue().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: rtn.clone()
            }));
            return output.read();
            return output.read();
        }
        fn r#_AlwaysModeledError_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Failure {
              error: ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::SimpleExtendableResourcesException {
                    message: ::dafny_runtime::string_utf16_of("Hard Coded Exception in src/dafny")
                  })
            }));
            return output.read();
            return output.read();
        }
        fn r#_AlwaysOpaqueError_k(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut obj =
                ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<dyn::std::any::Any>>::new();
            let mut _nw0: ::dafny_runtime::Object<
                super::r#_ExtendableResource_Compile::OpaqueMessage,
            > = super::r#_ExtendableResource_Compile::OpaqueMessage::_allocate_rcmut();
            super::r#_ExtendableResource_Compile::OpaqueMessage::_ctor(&_nw0);
            obj = ::dafny_runtime::MaybePlacebo::from(::dafny_runtime::UpcastTo::<
                ::dafny_runtime::Object<dyn::std::any::Any>,
            >::upcast_to(_nw0.clone()));
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Failure {
              error: ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::Opaque {
                    obj: obj.read()
                  })
            }));
            return output.read();
            return output.read();
        }
    }
}
pub mod r#_SimpleExtendableResourcesOperations_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn r#_ValidInternalConfig_q(
            config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>,
        ) -> bool {
            true
        }
        pub fn CreateExtendableResource(config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut resource = ::dafny_runtime::MaybePlacebo::<
                ::dafny_runtime::Object<super::r#_ExtendableResource_Compile::ExtendableResource>,
            >::new();
            let mut _nw1: ::dafny_runtime::Object<
                super::r#_ExtendableResource_Compile::ExtendableResource,
            > = super::r#_ExtendableResource_Compile::ExtendableResource::_allocate_rcmut();
            // expected `&mut ExtendableResource`, found `Object<ExtendableResource>`
            // super::r#_ExtendableResource_Compile::ExtendableResource::OfName(_nw1, input.name());
            resource = ::dafny_runtime::MaybePlacebo::from(_nw1.clone());
            let mut result: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput> = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput::CreateExtendableResourceOutput {
            resource: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>>::upcast_to(resource.read())
          });
            result = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput::CreateExtendableResourceOutput {
            resource: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>>::upcast_to(resource.read())
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: result.clone()
            }));
            return output.read();
            return output.read();
        }
        pub fn UseExtendableResource(config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource> = input.resource().clone();
            resource = input.resource().clone();
            let mut data = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out8 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out8 = ::dafny_runtime::MaybePlacebo::from(
                ::dafny_runtime::md!(resource).GetExtendableResourceData(input.input()),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out8.read());
            if valueOrError0.read().IsFailure() {
                output = ::dafny_runtime::MaybePlacebo::from(valueOrError0.read().PropagateFailure::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>>()/* <i>Coercion from ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>> to ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>></i> not yet implemented */);
                return output.read();
            };
            data = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput></i> not yet implemented */
            );
            let mut result: ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput> = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput::UseExtendableResourceOutput {
            output: data.read()
          });
            result = ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput::UseExtendableResourceOutput {
            output: data.read()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: result.clone()
            }));
            return output.read();
            return output.read();
        }
        pub fn UseExtendableResourceAlwaysModeledError(config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource> = input.resource().clone();
            resource = input.resource().clone();
            let mut result = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out9 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out9 = ::dafny_runtime::MaybePlacebo::from(
                ::dafny_runtime::md!(resource).AlwaysModeledError(input.input()),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out9.read());
            if valueOrError0.read().IsFailure() {
                output = ::dafny_runtime::MaybePlacebo::from(valueOrError0.read().PropagateFailure::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>()/* <i>Coercion from ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>> to ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>></i> not yet implemented */);
                return output.read();
            };
            result = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput></i> not yet implemented */
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: result.read()
            }));
            return output.read();
            return output.read();
        }
        pub fn UseExtendableResourceAlwaysMultipleErrors(config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource> = input.resource().clone();
            resource = input.resource().clone();
            let mut result = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out10 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out10 = ::dafny_runtime::MaybePlacebo::from(
                ::dafny_runtime::md!(resource).AlwaysMultipleErrors(input.input()),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out10.read());
            if valueOrError0.read().IsFailure() {
                output = ::dafny_runtime::MaybePlacebo::from(valueOrError0.read().PropagateFailure::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>()/* <i>Coercion from ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>> to ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>></i> not yet implemented */);
                return output.read();
            };
            result = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput></i> not yet implemented */
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: result.read()
            }));
            return output.read();
            return output.read();
        }
        pub fn UseExtendableResourceAlwaysOpaqueError(config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut resource: ::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource> = input.resource().clone();
            resource = input.resource().clone();
            let mut result = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>::new();
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out11 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            _out11 = ::dafny_runtime::MaybePlacebo::from(
                ::dafny_runtime::md!(resource).AlwaysOpaqueError(input.input()),
            );
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out11.read());
            if valueOrError0.read().IsFailure() {
                output = ::dafny_runtime::MaybePlacebo::from(valueOrError0.read().PropagateFailure::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>>()/* <i>Coercion from ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>> to ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>></i> not yet implemented */);
                return output.read();
            };
            result = ::dafny_runtime::MaybePlacebo::from(
                valueOrError0.read().Extract(), /* <i>Coercion from T to ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput></i> not yet implemented */
            );
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: result.read()
            }));
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
                    write!(
                        _formatter,
                        "r#_SimpleExtendableResourcesOperations_Compile.Config.Config"
                    )?;
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
pub mod r#_simple_dextendable_dresources_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn DefaultSimpleExtendableResourcesConfig() -> ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::SimpleExtendableResourcesConfig>{
            ::std::rc::Rc::new(super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::SimpleExtendableResourcesConfig::SimpleExtendableResourcesConfig {})
        }
        pub fn SimpleExtendableResources(config: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::SimpleExtendableResourcesConfig>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
            let mut internalConfig: ::std::rc::Rc<
                super::r#_SimpleExtendableResourcesOperations_Compile::Config,
            > = ::std::rc::Rc::new(
                super::r#_SimpleExtendableResourcesOperations_Compile::Config::Config {},
            );
            internalConfig = ::std::rc::Rc::new(
                super::r#_SimpleExtendableResourcesOperations_Compile::Config::Config {},
            );
            let mut client = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient>>::new();
            let mut _nw2: ::dafny_runtime::Object<super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient> = super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient::_allocate_rcmut();
            super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient::_ctor(&_nw2, &internalConfig);
            client = ::dafny_runtime::MaybePlacebo::from(_nw2.clone());
            res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
              value: client.read()
            }));
            return res.read();
            return res.read();
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    pub struct SimpleExtendableResourcesClient {
        pub r#__i_config:
            ::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>,
    }

    impl SimpleExtendableResourcesClient {
        pub fn _allocate_rcmut() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_rcmut::<Self>()
        }
        pub fn _ctor(
            this: &::dafny_runtime::Object<Self>,
            config: &::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config>,
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
        pub fn config(
            &self,
        ) -> ::std::rc::Rc<super::r#_SimpleExtendableResourcesOperations_Compile::Config> {
            self.r#__i_config.clone()
        }
    }

    impl super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::ISimpleExtendableResourcesClient
    for super::r#_simple_dextendable_dresources_dinternaldafny::SimpleExtendableResourcesClient {
    fn CreateExtendableResource(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      let mut _out12 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::CreateExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      _out12 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleExtendableResourcesOperations_Compile::_default::CreateExtendableResource(&self.config(), input));
      output = ::dafny_runtime::MaybePlacebo::from(_out12.read());
      return output.read();
    }
    fn UseExtendableResource(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      let mut _out13 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      _out13 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleExtendableResourcesOperations_Compile::_default::UseExtendableResource(&self.config(), input));
      output = ::dafny_runtime::MaybePlacebo::from(_out13.read());
      return output.read();
    }
    fn UseExtendableResourceAlwaysModeledError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      let mut _out14 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      _out14 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleExtendableResourcesOperations_Compile::_default::UseExtendableResourceAlwaysModeledError(&self.config(), input));
      output = ::dafny_runtime::MaybePlacebo::from(_out14.read());
      return output.read();
    }
    fn UseExtendableResourceAlwaysMultipleErrors(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      let mut _out15 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      _out15 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleExtendableResourcesOperations_Compile::_default::UseExtendableResourceAlwaysMultipleErrors(&self.config(), input));
      output = ::dafny_runtime::MaybePlacebo::from(_out15.read());
      return output.read();
    }
    fn UseExtendableResourceAlwaysOpaqueError(&mut self, input: &::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::UseExtendableResourceErrorsInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      let mut _out16 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>, ::std::rc::Rc<super::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>>::new();
      _out16 = ::dafny_runtime::MaybePlacebo::from(super::r#_SimpleExtendableResourcesOperations_Compile::_default::UseExtendableResourceAlwaysOpaqueError(&self.config(), input));
      output = ::dafny_runtime::MaybePlacebo::from(_out16.read());
      return output.read();
    }
  }
}
pub mod _module {}
