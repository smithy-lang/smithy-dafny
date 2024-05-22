#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub use dafny_runtime;
pub use dafny_standard_library;
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes {
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
                "simple.types.smithyboolean.internaldafny.types.DafnyCallEvent("
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
     datatype GetBooleanInput = | GetBooleanInput (
      nameonly value: Option<boolean> := Option.None
    )
    */
    #[derive(Clone)]
    pub enum GetBooleanInput {
        GetBooleanInput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>,
        },
    }
    impl ::std::convert::AsRef<GetBooleanInput> for &GetBooleanInput {
        fn as_ref(&self) -> Self {
            self
        }
    }
    impl GetBooleanInput {
        pub fn value(&self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                GetBooleanInput::GetBooleanInput { value } => value.clone(),
            }
        }
    }
    impl ::core::fmt::Debug for GetBooleanInput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetBooleanInput {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyboolean.internaldafny.types.GetBooleanInput(value := "
            )?;
            self.value().fmt_print(f, false)?;
            write!(f, ")")
        }
    }
    impl PartialEq<GetBooleanInput> for GetBooleanInput {
        fn eq(&self, other: &GetBooleanInput) -> bool {
            self.value() == other.value()
        }
    }
    impl Eq for GetBooleanInput {}
    impl ::core::hash::Hash for GetBooleanInput {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value().hash(state);
        }
    }

    /*
    datatype GetBooleanOutput = | GetBooleanOutput (
    nameonly value: Option<boolean> := Option.None
    ) */
    #[derive(Clone)]
    pub enum GetBooleanOutput {
        GetBooleanOutput {
            value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>,
        },
    }
    impl GetBooleanOutput {
        pub fn value(&self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                GetBooleanOutput::GetBooleanOutput { value } => value.clone(),
            }
        }
    }
    impl ::std::convert::AsRef<GetBooleanOutput> for &GetBooleanOutput {
        fn as_ref(&self) -> Self {
            self
        }
    }
    impl ::core::fmt::Debug for GetBooleanOutput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetBooleanOutput {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyboolean.internaldafny.types.GetBooleanOutput(value := "
            )?;
            self.value().fmt_print(f, false)?;
            write!(f, ")")
        }
    }
    impl PartialEq<GetBooleanOutput> for GetBooleanOutput {
        fn eq(&self, other: &GetBooleanOutput) -> bool {
            self.value() == other.value()
        }
    }
    impl Eq for GetBooleanOutput {}
    impl ::core::hash::Hash for GetBooleanOutput {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value().hash(state);
        }
    }

    /*
    datatype SimpleBooleanConfig = | SimpleBooleanConfig (
    ) */
    #[derive(Clone)]
    pub enum SimpleBooleanConfig {
        SimpleBooleanConfig {},
    }

    impl ::std::convert::AsRef<SimpleBooleanConfig> for &SimpleBooleanConfig {
        fn as_ref(&self) -> Self {
            self
        }
    }

    impl ::core::fmt::Debug for SimpleBooleanConfig {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.debug_struct("SimpleBooleanConfig").finish()
        }
    }

    impl ::dafny_runtime::DafnyPrint for SimpleBooleanConfig {
        fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
            write!(
                f,
                "simple.types.smithyboolean.internaldafny.types.SimpleBooleanConfig()"
            )
        }
    }
    impl PartialEq<SimpleBooleanConfig> for SimpleBooleanConfig {
        fn eq(&self, other: &SimpleBooleanConfig) -> bool {
            true
        }
    }
    impl Eq for SimpleBooleanConfig {}

    impl ::core::hash::Hash for SimpleBooleanConfig {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {}
    }

    pub struct ISimpleTypesBooleanClientCallHistory {}
    impl ISimpleTypesBooleanClientCallHistory {
        fn ctor(this: *mut ISimpleTypesBooleanClientCallHistory) {}
    }
    pub trait ISimpleTypesBooleanClient {
        fn GetBoolean(
            self: &Self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>,
            >,
        >;
    }
    /*
    datatype Error =
    | CollectionOfErrors(list: seq<Error>, nameonly message: boolean)
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

mod r#_SimpleBooleanImpl_Compile {
    pub struct _default {}
    impl _default {
        pub fn new() -> Self {
            _default {}
        }

        pub fn _allocated() -> *mut Self {
            ::dafny_runtime::allocate::<Self>()
        }

        pub fn GetBoolean(
            config: &::std::rc::Rc<super::r#_SimpleBooleanImpl_Compile::Config>,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>>>>::new();
            let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput::GetBooleanOutput {
            value: input.value().clone()
          });
            res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput::GetBooleanOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>>::Success {
              value: res.clone()
            }));
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
            write!(_formatter, "SimpleBooleanImpl_Compile.__default")
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
                    write!(_formatter, "SimpleBooleanImpl_Compile.Config.Config")?;
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
// SimpleBoolean
pub mod r#_simple_dtypes_dsmithyboolean_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn new() -> Self {
            _default {}
        }

        pub fn DefaultSimpleBooleanConfig(
        ) -> super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::SimpleBooleanConfig
        {
            super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::SimpleBooleanConfig::SimpleBooleanConfig{}
        }

        /*method SimpleBoolean(config: SimpleBooleanConfig)
        returns (res: Result<ISimpleTypesBooleanClient, Error>) {
            var client := new SimpleBooleanClient(Operations.Config);
            return Success(client);
        } */
    pub fn SimpleBoolean(config: &::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::SimpleBooleanConfig>)
        -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<*mut dyn super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>>>{
            let client: *mut SimpleBooleanClient =
                ::dafny_runtime::allocate::<SimpleBooleanClient>();
            SimpleBooleanClient::_ctor(
                client,
                &::std::rc::Rc::new(super::r#_SimpleBooleanImpl_Compile::Config::Config {}),
            );
            let v = client as *mut dyn super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient;
            // build a success
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<*mut dyn super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>>::Success{
          value: v
      })
        }
    }

    struct SimpleBooleanClient {
        r#_i_config: ::std::rc::Rc<super::r#_SimpleBooleanImpl_Compile::Config>,
    }

    impl SimpleBooleanClient {
        fn _ctor(
            this: *mut SimpleBooleanClient,
            config: &::std::rc::Rc<super::r#_SimpleBooleanImpl_Compile::Config>,
        ) {
            let mut _i_set_config = false;
            ::dafny_runtime::update_field_uninit!(this, r#_i_config, _i_set_config, config.clone());
        }
        fn config(&self) -> ::std::rc::Rc<super::r#_SimpleBooleanImpl_Compile::Config> {
            self.r#_i_config.clone()
        }
    }

    impl super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient
        for SimpleBooleanClient
    {
        fn GetBoolean(
            self: &Self,
            input: &::std::rc::Rc<
                super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanInput,
            >,
        ) -> ::std::rc::Rc<
            super::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::GetBooleanOutput,
                >,
                ::std::rc::Rc<super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::Error>,
            >,
        > {
            super::r#_SimpleBooleanImpl_Compile::_default::GetBoolean(&self.config(), input)
        }
    }
    ::dafny_runtime::UpcastTo!(
        SimpleBooleanClient,
        dyn super::r#_simple_dtypes_dsmithyboolean_dinternaldafny_dtypes::ISimpleTypesBooleanClient
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
        pub fn CreateBooleanSome(
            b: bool,
        ) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some { value: b })
        }
        pub fn CreateBooleanNone() -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
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
