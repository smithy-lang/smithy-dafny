#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub use dafny_standard_library::implementation_from_dafny::*;

pub mod simple {
    pub mod types {
        pub mod blob {
            pub mod internaldafny {
                pub use crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleBlobConfig() -> ::std::rc::Rc<
                        crate::simple::types::blob::internaldafny::types::SimpleBlobConfig,
                    > {
                        ::std::rc::Rc::new(crate::simple::types::blob::internaldafny::types::SimpleBlobConfig::SimpleBlobConfig {})
                    }
                    pub fn SimpleBlob(
                        config: &::std::rc::Rc<
                            crate::simple::types::blob::internaldafny::types::SimpleBlobConfig,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::dafny_runtime::Object<
                                crate::simple::types::blob::internaldafny::SimpleBlobClient,
                            >,
                            ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                        >,
                    > {
                        let mut res = ::dafny_runtime::MaybePlacebo::<
                            ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Result<
                                    ::dafny_runtime::Object<
                                        crate::simple::types::blob::internaldafny::SimpleBlobClient,
                                    >,
                                    ::std::rc::Rc<
                                        crate::simple::types::blob::internaldafny::types::Error,
                                    >,
                                >,
                            >,
                        >::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<
                            ::dafny_runtime::Object<
                                crate::simple::types::blob::internaldafny::SimpleBlobClient,
                            >,
                        >::new();
                        let mut _nw0: ::dafny_runtime::Object<crate::simple::types::blob::internaldafny::SimpleBlobClient> = crate::simple::types::blob::internaldafny::SimpleBlobClient::_allocate_object();
                        crate::simple::types::blob::internaldafny::SimpleBlobClient::_ctor(
                            &_nw0,
                            &::std::rc::Rc::new(
                                crate::r#_SimpleBlobImpl_Compile::Config::Config {},
                            ),
                        );
                        client = ::dafny_runtime::MaybePlacebo::from(_nw0.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                            crate::r#_Wrappers_Compile::Result::<
                                ::dafny_runtime::Object<
                                    crate::simple::types::blob::internaldafny::SimpleBlobClient,
                                >,
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::Error,
                                >,
                            >::Success {
                                value: client.read(),
                            },
                        ));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleBlobClient {
                    pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleBlobImpl_Compile::Config>,
                }

                impl SimpleBlobClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::blob::internaldafny::SimpleBlobClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleBlobImpl_Compile::Config>,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleBlobImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any> for crate::simple::types::blob::internaldafny::SimpleBlobClient {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesBlobClient for crate::simple::types::blob::internaldafny::SimpleBlobClient {
                    fn GetBlob(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::types::blob::internaldafny::types::GetBlobInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                            >,
                            ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                        >,
                    > {
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleBlobImpl_Compile::_default::GetBlob(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn GetBlobKnownValueTest(
                        &mut self,
                        input: &::std::rc::Rc<
                            crate::simple::types::blob::internaldafny::types::GetBlobInput,
                        >,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::std::rc::Rc<
                                crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                            >,
                            ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                        >,
                    > {
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>, ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleBlobImpl_Compile::_default::GetBlobKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesBlobClient>
                    for crate::simple::types::blob::internaldafny::SimpleBlobClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClient);
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
                                    write!(_formatter, "simple.types.blob.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetBlobInput {
                        GetBlobInput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                            >,
                        },
                    }

                    impl GetBlobInput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        > {
                            match self {
                                GetBlobInput::GetBlobInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetBlobInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetBlobInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetBlobInput::GetBlobInput { value } => {
                                    write!(_formatter, "simple.types.blob.internaldafny.types.GetBlobInput.GetBlobInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetBlobInput {}

                    impl Hash for GetBlobInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetBlobInput::GetBlobInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetBlobInput {
                        fn default() -> GetBlobInput {
                            GetBlobInput::GetBlobInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetBlobInput> for &GetBlobInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetBlobOutput {
                        GetBlobOutput {
                            value: ::std::rc::Rc<
                                crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                            >,
                        },
                    }

                    impl GetBlobOutput {
                        pub fn value(
                            &self,
                        ) -> &::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
                        > {
                            match self {
                                GetBlobOutput::GetBlobOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetBlobOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetBlobOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetBlobOutput::GetBlobOutput { value } => {
                                    write!(_formatter, "simple.types.blob.internaldafny.types.GetBlobOutput.GetBlobOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetBlobOutput {}

                    impl Hash for GetBlobOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetBlobOutput::GetBlobOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetBlobOutput {
                        fn default() -> GetBlobOutput {
                            GetBlobOutput::GetBlobOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetBlobOutput> for &GetBlobOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleBlobConfig {
                        SimpleBlobConfig {},
                    }

                    impl SimpleBlobConfig {}

                    impl Debug for SimpleBlobConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleBlobConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleBlobConfig::SimpleBlobConfig {} => {
                                    write!(_formatter, "simple.types.blob.internaldafny.types.SimpleBlobConfig.SimpleBlobConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleBlobConfig {}

                    impl Hash for SimpleBlobConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleBlobConfig::SimpleBlobConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleBlobConfig {
                        fn default() -> SimpleBlobConfig {
                            SimpleBlobConfig::SimpleBlobConfig {}
                        }
                    }

                    impl AsRef<SimpleBlobConfig> for &SimpleBlobConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesBlobClientCallHistory {}

                    impl ISimpleTypesBlobClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::blob::internaldafny::types::ISimpleTypesBlobClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesBlobClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetBlob(
                            &mut self,
                            input: &::std::rc::Rc<
                                crate::simple::types::blob::internaldafny::types::GetBlobInput,
                            >,
                        ) -> ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                                >,
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::Error,
                                >,
                            >,
                        >;
                        fn GetBlobKnownValueTest(
                            &mut self,
                            input: &::std::rc::Rc<
                                crate::simple::types::blob::internaldafny::types::GetBlobInput,
                            >,
                        ) -> ::std::rc::Rc<
                            crate::r#_Wrappers_Compile::Result<
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                                >,
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::Error,
                                >,
                            >,
                        >;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::blob::internaldafny::types::Error,
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
                            ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
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
                                    write!(_formatter, "simple.types.blob.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                        "simple.types.blob.internaldafny.types.Error.Opaque("
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
                        ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>;
                }
            }
        }
    }
}
pub mod r#_SimpleBlobImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetBlob(
            config: &::std::rc::Rc<crate::r#_SimpleBlobImpl_Compile::Config>,
            input: &::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobInput>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>,
                ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(input.value().value());
            let mut res: ::std::rc::Rc<
                crate::simple::types::blob::internaldafny::types::GetBlobOutput,
            > = ::std::rc::Rc::new(
                crate::simple::types::blob::internaldafny::types::GetBlobOutput::GetBlobOutput {
                    value: input.value().clone(),
                },
            );
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(res.value().value());
            let mut _e00: ::dafny_runtime::Sequence<u8> = res.value().value().clone();
            let mut _e10: ::dafny_runtime::Sequence<u8> = input.value().value().clone();
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
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>,
                    ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetBlobKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleBlobImpl_Compile::Config>,
            input: &::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobInput>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>,
                ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::blob::internaldafny::types::GetBlobOutput,
                        >,
                        ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(input.value().value());
            let mut _e01: ::dafny_runtime::Sequence<u8> = input.value().value().clone();
            let mut _e11: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![0, 2, 4];
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
            let mut res: ::std::rc::Rc<
                crate::simple::types::blob::internaldafny::types::GetBlobOutput,
            > = ::std::rc::Rc::new(
                crate::simple::types::blob::internaldafny::types::GetBlobOutput::GetBlobOutput {
                    value: input.value().clone(),
                },
            );
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            crate::r#_SimpleBlobImpl_Compile::_default::ValidateBlobType(res.value().value());
            let mut _e02: ::dafny_runtime::Sequence<u8> = res.value().value().clone();
            let mut _e12: ::dafny_runtime::Sequence<u8> = input.value().value().clone();
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
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::GetBlobOutput>,
                    ::std::rc::Rc<crate::simple::types::blob::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn ValidateBlobType(input: &::dafny_runtime::Sequence<u8>) -> () {
            if !(input.cardinality() >= ::dafny_runtime::int!(0)) {
                panic!("Halt")
            };
            let mut _hi0: ::dafny_runtime::DafnyInt = input.cardinality();
            for i in ::dafny_runtime::integer_range(::dafny_runtime::int!(0), _hi0.clone()) {
                let mut inputElement: u8 = input.get(&i);
                if !(inputElement >= 0) {
                    panic!("Halt")
                }
            }
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
                    write!(_formatter, "SimpleBlobImpl_Compile.Config.Config")?;
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
