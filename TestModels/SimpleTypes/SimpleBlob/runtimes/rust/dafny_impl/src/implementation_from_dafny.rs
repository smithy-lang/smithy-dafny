#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_runtime;
pub use dafny_standard_library;
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes {
    /* datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O) */
    #[derive(Clone)]
    pub struct DafnyCallEvent<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> {
        input: I,
        output: O,
    }
    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::core::fmt::Debug
        for DafnyCallEvent<I, O>
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("DafnyCallEvent")
                .field("input", &self.input)
                .field("output", &self.output)
                .finish()
        }
    }
    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::dafny_runtime::DafnyPrint
        for DafnyCallEvent<I, O>
    {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyblob.internaldafny.types.DafnyCallEvent("
            )?;
            self.input.fmt_print(f, false)?;
            write!(f, ",")?;
            self.output.fmt_print(f, false)?;
            write!(f, ")")
        }
    }
    impl<I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq>
        PartialEq<DafnyCallEvent<I, O>> for DafnyCallEvent<I, O>
    {
        fn eq(&self, other: &DafnyCallEvent<I, O>) -> bool {
            self.input == other.input && self.output == other.output
        }
    }
    impl<I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq> Eq for DafnyCallEvent<I, O> {}
    impl<I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq> ::core::hash::Hash
        for DafnyCallEvent<I, O>
    {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.input.hash(state);
            self.output.hash(state);
        }
    }

    /*
     datatype GetBlobInput = | GetBlobInput (
      nameonly value: Option<blob> := Option.None
    )
    */
    #[derive(Clone)]
    pub enum GetBlobInput {
        GetBlobInput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
            >,
        },
    }
    impl ::std::convert::AsRef<GetBlobInput> for &GetBlobInput {
        fn as_ref(&self) -> Self {
            self
        }
    }
    impl GetBlobInput {
        pub fn value(
            &self,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
        > {
            match self {
                GetBlobInput::GetBlobInput { value } => value.clone(),
            }
        }
    }
    impl ::core::fmt::Debug for GetBlobInput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetBlobInput {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyblob.internaldafny.types.GetBlobInput(value := "
            )?;
            self.value().fmt_print(f, false)?;
            write!(f, ")")
        }
    }
    impl PartialEq<GetBlobInput> for GetBlobInput {
        fn eq(&self, other: &GetBlobInput) -> bool {
            self.value() == other.value()
        }
    }
    impl Eq for GetBlobInput {}
    impl ::core::hash::Hash for GetBlobInput {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value().hash(state);
        }
    }

    /*
    datatype GetBlobOutput = | GetBlobOutput (
    nameonly value: Option<blob> := Option.None
    ) */
    #[derive(Clone)]
    pub enum GetBlobOutput {
        GetBlobOutput {
            value: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
            >,
        },
    }
    impl GetBlobOutput {
        pub fn value(
            &self,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
        > {
            match self {
                GetBlobOutput::GetBlobOutput { value } => value.clone(),
            }
        }
    }
    impl ::std::convert::AsRef<GetBlobOutput> for &GetBlobOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }
    impl ::core::fmt::Debug for GetBlobOutput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetBlobOutput {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyblob.internaldafny.types.GetBlobOutput(value := "
            )?;
            self.value().fmt_print(f, false)?;
            write!(f, ")")
        }
    }
    impl PartialEq<GetBlobOutput> for GetBlobOutput {
        fn eq(&self, other: &GetBlobOutput) -> bool {
            self.value() == other.value()
        }
    }
    impl Eq for GetBlobOutput {}
    impl ::core::hash::Hash for GetBlobOutput {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value().hash(state);
        }
    }

    /*
    datatype SimpleBlobConfig = | SimpleBlobConfig (
    ) */
    #[derive(Clone)]
    pub enum SimpleBlobConfig {
        SimpleBlobConfig {},
    }

    impl ::std::convert::AsRef<SimpleBlobConfig> for &SimpleBlobConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    impl ::core::fmt::Debug for SimpleBlobConfig {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("SimpleBlobConfig").finish()
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleBlobConfig {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyblob.internaldafny.types.SimpleBlobConfig()"
            )
        }
    }
    impl PartialEq<SimpleBlobConfig> for SimpleBlobConfig {
        fn eq(&self, other: &SimpleBlobConfig) -> bool {
            true
        }
    }
    impl Eq for SimpleBlobConfig {}

    impl ::core::hash::Hash for SimpleBlobConfig {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {}
    }

    pub struct ISimpleTypesBlobClientCallHistory {}
    impl ISimpleTypesBlobClientCallHistory {
        fn ctor(this: *mut ISimpleTypesBlobClientCallHistory) {}
    }
    pub trait ISimpleTypesBlobClient {
        fn GetBlob(
            self: &Self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>,
            >,
        >;
    }
    /*
    datatype Error =
    | CollectionOfErrors(list: seq<Error>, nameonly message: blob)
    | Opaque(obj: object)
    */
    #[derive(Clone)]
    pub enum Error {
        CollectionOfErrors {
            list: ::dafny_runtime::Sequence<Error>,
            message: bool,
        },
        Opaque {
            obj: *mut dyn ::std::any::Any,
        },
    }
    impl ::core::fmt::Debug for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Error::CollectionOfErrors { list, message } => f
                    .debug_struct("Error::CollectionOfErrors")
                    .field("list", list)
                    .field("message", message)
                    .finish(),
                Error::Opaque { obj } => f.debug_struct("Error::Opaque").field("obj", obj).finish(),
            }
        }
    }
    impl ::dafny_runtime::DafnyPrint for Error {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            match self {
                Error::CollectionOfErrors { list, message } => {
                    write!(f, "Error::CollectionOfErrors(list := ")?;
                    list.fmt_print(f, false)?;
                    write!(f, ", message := ")?;
                    message.fmt_print(f, false)?;
                    write!(f, ")")
                }
                Error::Opaque { obj } => {
                    write!(f, "Error::Opaque(obj := ")?;
                    obj.fmt_print(f, false)?;
                    write!(f, ")")
                }
            }
        }
    }
    impl PartialEq<Error> for Error {
        fn eq(&self, other: &Error) -> bool {
            match self {
                Error::CollectionOfErrors { list, message } => match other {
                    Error::CollectionOfErrors {
                        list: other_list,
                        message: other_message,
                    } => list == other_list && message == other_message,
                    _ => false,
                },
                Error::Opaque { obj } => match other {
                    Error::Opaque { obj: other_obj } => obj == other_obj,
                    _ => false,
                },
            }
        }
    }
    impl Eq for Error {}
    impl ::core::hash::Hash for Error {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            match self {
                Error::CollectionOfErrors { list, message } => {
                    list.hash(state);
                    message.hash(state);
                }
                Error::Opaque { obj } => obj.hash(state),
            }
        }
    }

    pub type OpaqueError = Error;
}

mod r#_SimpleBlobImpl_Compile {
    pub struct _default {}
    impl _default {
        pub fn new() -> Self {
            _default {}
        }

        pub fn _allocated() -> *mut Self {
            ::dafny_runtime::allocate::<Self>()
        }

        pub fn GetBlob(
            config: &::std::rc::Rc<super::r#_SimpleBlobImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>>>>::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput::GetBlobOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput::GetBlobOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                super::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput,
                    >,
                    ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
            return output.read();
        }
    }
    impl ::std::default::Default for _default {
        fn default() -> Self {
            _default::new()
        }
    }
    impl ::dafny_runtime::DafnyPrint for _default {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            write!(_formatter, "SimpleBlobImpl_Compile.__default")
        }
    }
    impl ::std::cmp::PartialEq for _default {
        fn eq(&self, other: &Self) -> bool {
            ::std::ptr::eq(self, other)
        }
    }
    #[derive(PartialEq, Clone)]
    pub enum Config {
        Config {},
    }
    impl Config {}

    impl ::dafny_runtime::DafnyPrint for Config {
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
// SimpleBlob
pub mod r#_simple_dtypes_dsmithyblob_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn new() -> Self {
            _default {}
        }

        pub fn DefaultSimpleBlobConfig(
        ) -> super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::SimpleBlobConfig {
            super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::SimpleBlobConfig::SimpleBlobConfig{}
        }

        /*method SimpleBlob(config: SimpleBlobConfig)
        returns (res: Result<ISimpleTypesBlobClient, Error>) {
            var client := new SimpleBlobClient(Operations.Config);
            return Success(client);
        } */
    pub fn SimpleBlob(config: &::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::SimpleBlobConfig>)
        -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<*mut dyn super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::ISimpleTypesBlobClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>>>{
            let client: *mut SimpleBlobClient = ::dafny_runtime::allocate::<SimpleBlobClient>();
            SimpleBlobClient::_ctor(
                client,
                &::std::rc::Rc::new(super::r#_SimpleBlobImpl_Compile::Config::Config {}),
            );
            let v = client as *mut dyn super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::ISimpleTypesBlobClient;
            // build a success
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<*mut dyn super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::ISimpleTypesBlobClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>>::Success{
          value: v
      })
        }
    }

    struct SimpleBlobClient {
        r#_i_config: ::std::rc::Rc<super::r#_SimpleBlobImpl_Compile::Config>,
    }

    impl SimpleBlobClient {
        fn _ctor(
            this: *mut SimpleBlobClient,
            config: &::std::rc::Rc<super::r#_SimpleBlobImpl_Compile::Config>,
        ) {
            let mut _i_set_config = false;
            ::dafny_runtime::update_field_uninit!(this, r#_i_config, _i_set_config, config.clone());
        }
        fn config(&self) -> ::std::rc::Rc<super::r#_SimpleBlobImpl_Compile::Config> {
            self.r#_i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::ISimpleTypesBlobClient
        for SimpleBlobClient
    {
        fn GetBlob(
            self: &Self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::GetBlobOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::Error>,
            >,
        > {
            super::r#_SimpleBlobImpl_Compile::_default::GetBlob(&self.config(), input)
        }
    }
    ::dafny_runtime::UpcastTo!(
        SimpleBlobClient,
        dyn super::r#_simple_dtypes_dsmithyblob_dinternaldafny_dtypes::ISimpleTypesBlobClient
    );
}

mod r#_StandardLibraryInterop_Compile {
    pub struct WrappersInterop {}

    impl WrappersInterop {
        pub fn new() -> Self {
            WrappersInterop {}
        }
        pub fn _allocated() -> *mut Self {
            ::dafny_runtime::allocate::<Self>()
        }
        pub fn CreateStringSome(
            s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Some {
                value: s.clone(),
            })
        }
        pub fn CreateStringNone() -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::None {})
        }
        pub fn CreateBlobSome(
            b: ::dafny_runtime::Sequence<::std::primitive::u8>,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::std::primitive::u8>,
            >::Some {
                value: b,
            })
        }
        pub fn CreateBlobNone() -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::primitive::u8>>,
        > {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::std::primitive::u8>,
            >::None {})
        }
    }

    impl ::std::default::Default for WrappersInterop {
        fn default() -> Self {
            WrappersInterop::new()
        }
    }

    impl ::dafny_runtime::DafnyPrint for WrappersInterop {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            write!(_formatter, "StandardLibraryInterop_Compile.WrappersInterop")
        }
    }

    impl ::std::cmp::PartialEq for WrappersInterop {
        fn eq(&self, other: &Self) -> bool {
            ::std::ptr::eq(self, other)
        }
    }
}
mod _module {}
