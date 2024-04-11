#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub extern crate dafny_runtime;
pub extern crate dafny_standard_library;
pub use dafny_standard_library::implementation_from_dafny::*;

pub mod r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes {
  /* datatype DafnyCallEvent<I, O> = DafnyCallEvent(input: I, output: O) */
    #[derive(Clone)]
    pub struct DafnyCallEvent<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> {
      input: I,
      output: O
    }
    impl <I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::core::fmt::Debug for
      DafnyCallEvent<I, O> {
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DafnyCallEvent").field("input", &self.input).field("output", &self.output).finish()
      }
    }
    impl <I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::dafny_runtime::DafnyPrint for
      DafnyCallEvent<I, O> {
      fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        write!(f, "simple.types.smithystring.internaldafny.types.DafnyCallEvent(")?;
        self.input.fmt_print(f, false)?;
        write!(f, ",")?;
        self.output.fmt_print(f, false)?;
        write!(f, ")")
      }
    }
    impl <I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq>
      PartialEq<DafnyCallEvent<I, O>> for DafnyCallEvent<I, O> {
        fn eq(&self, other: &DafnyCallEvent<I, O>) -> bool {
          self.input == other.input && self.output == other.output
        }
    }
    impl <I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq> Eq for DafnyCallEvent<I, O> {}
    impl <I: ::dafny_runtime::DafnyTypeEq, O: ::dafny_runtime::DafnyTypeEq> ::core::hash::Hash for DafnyCallEvent<I, O> {
      fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.input.hash(state);
        self.output.hash(state);
      }
    }

    /*
     datatype GetStringInput = | GetStringInput (
      nameonly value: Option<string> := Option.None
    )
    */
    #[derive(Clone)]
    pub enum GetStringInput {
      GetStringInput { value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::DafnyStringUTF16>> }
    }
    impl ::std::convert::AsRef<GetStringInput> for &GetStringInput {
      fn as_ref(&self) -> Self {
        self
      }
    }
    impl GetStringInput {
      pub fn value(&self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::DafnyStringUTF16>> {
        match self {
          GetStringInput::GetStringInput { value } => {
            value.clone()
          }
        }
      }
    }
    impl ::core::fmt::Debug for GetStringInput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetStringInput {
      fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        write!(f, "simple.types.smithystring.internaldafny.types.GetStringInput(value := ")?;
        self.value().fmt_print(f, false)?;
        write!(f, ")")
      }
    }
    impl PartialEq<GetStringInput> for GetStringInput {
        fn eq(&self, other: &GetStringInput) -> bool {
          self.value() == other.value()
        }
    }
    impl Eq for GetStringInput {}
    impl ::core::hash::Hash for GetStringInput {
      fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value().hash(state);
      }
    }
    
    /*
    datatype GetStringOutput = | GetStringOutput (
    nameonly value: Option<string> := Option.None
    ) */
    #[derive(Clone)]
    pub enum GetStringOutput {
      GetStringOutput {
        value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::DafnyStringUTF16>>
      }
    }
    impl GetStringOutput {
      pub fn value(&self) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::DafnyStringUTF16>> {
        match self {
          GetStringOutput::GetStringOutput { value } => {
            value.clone()
          }
        }
      }
    }
    impl ::std::convert::AsRef<GetStringOutput> for &GetStringOutput {
      fn as_ref(&self) -> Self {
        self
      }
    }
    impl ::core::fmt::Debug for GetStringOutput {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          ::dafny_runtime::DafnyPrint::fmt_print(self, f, false)
        }
    }
    impl ::dafny_runtime::DafnyPrint for GetStringOutput {
      fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        write!(f, "simple.types.smithystring.internaldafny.types.GetStringOutput(value := ")?;
        self.value().fmt_print(f, false)?;
        write!(f, ")")
      }
    }
    impl PartialEq<GetStringOutput> for GetStringOutput {
        fn eq(&self, other: &GetStringOutput) -> bool {
          self.value() == other.value()
        }
    }
    impl Eq for GetStringOutput {}
    impl ::core::hash::Hash for GetStringOutput {
      fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value().hash(state);
      }
    }

    
    /*
    datatype SimpleStringConfig = | SimpleStringConfig (
    ) */
    #[derive(Clone)]
    pub enum SimpleStringConfig {
      SimpleStringConfig {}
    }
    impl ::std::convert::AsRef<SimpleStringConfig> for &SimpleStringConfig {
      fn as_ref(&self) -> Self {
        self
      }
    }
    impl ::core::fmt::Debug for SimpleStringConfig {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          f.debug_struct("SimpleStringConfig").finish()
        }
    }
    impl ::dafny_runtime::DafnyPrint for SimpleStringConfig {
      fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        write!(f, "simple.types.smithystring.internaldafny.types.SimpleStringConfig()")
      }
    }
    impl PartialEq<SimpleStringConfig> for SimpleStringConfig {
        fn eq(&self, other: &SimpleStringConfig) -> bool {
          true
        }
    }
    impl Eq for SimpleStringConfig {}
    impl ::core::hash::Hash for SimpleStringConfig {
      fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
      }
    }

    pub struct ISimpleTypesStringClientCallHistory {
    }
    impl ISimpleTypesStringClientCallHistory {
      fn ctor(this: *mut ISimpleTypesStringClientCallHistory) {
      }
    }
    pub trait ISimpleTypesStringClient {
      fn GetString(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>;
      fn GetStringSingleValue(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>;
      fn GetStringUTF8(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>;
    }
    /*
    datatype Error =
    | CollectionOfErrors(list: seq<Error>, nameonly message: string)
    | Opaque(obj: object)
    */
    #[derive(Clone)]
    pub enum Error {
      CollectionOfErrors{list: ::dafny_runtime::Sequence<Error>, message: ::dafny_runtime::DafnyStringUTF16},
      Opaque{obj: *mut dyn ::std::any::Any}
    }
    impl ::core::fmt::Debug for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
          match self {
            Error::CollectionOfErrors{list, message} => f.debug_struct("Error::CollectionOfErrors").field("list", list).field("message", message).finish(),
            Error::Opaque{obj} => f.debug_struct("Error::Opaque").field("obj", obj).finish()
          }
        }
    }
    impl ::dafny_runtime::DafnyPrint for Error {
      fn fmt_print(&self, f: &mut std::fmt::Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        match self {
          Error::CollectionOfErrors{list, message} => {
            write!(f, "Error::CollectionOfErrors(list := ")?;
            list.fmt_print(f, false)?;
            write!(f, ", message := ")?;
            message.fmt_print(f, false)?;
            write!(f, ")")
          },
          Error::Opaque{obj} => {
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
            Error::CollectionOfErrors{list, message} => match other {
              Error::CollectionOfErrors{list: other_list, message: other_message} => list == other_list && message == other_message,
              _ => false
            },
            Error::Opaque{obj} => match other {
              Error::Opaque{obj: other_obj} => obj == other_obj,
              _ => false
            }
          }
        }
    }
    impl Eq for Error {}
    impl ::core::hash::Hash for Error {
      fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
          Error::CollectionOfErrors{list, message} => {
            list.hash(state);
            message.hash(state);
          },
          Error::Opaque{obj} => obj.hash(state)
        }
      }
    }

    pub type OpaqueError = Error;


}
mod r#_SimpleStringImpl_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn _allocated() -> *mut Self {
      ::dafny_runtime::allocate::<Self>()
    }
    pub fn GetString(config: &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>>::new();
      let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>::Success {
              value: res.clone()
            }));
      return output.read();
      return output.read();
    }
    pub fn GetStringSingleValue(config: &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>>::new();
      if !matches!(input.value().as_ref(), super::r#_Wrappers_Compile::Option::Some{ .. }) {
        panic!("Halt")
      };
      if !(input.value().value().clone() == ::dafny_runtime::string_utf16_of("TEST_SIMPLE_STRING_SINGLE_VALUE")) {
        panic!("Halt")
      };
      let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>::Success {
              value: res.clone()
            }));
      return output.read();
      return output.read();
    }
    pub fn GetStringUTF8(config: &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>>>::new();
      if !matches!(input.value().as_ref(), super::r#_Wrappers_Compile::Option::Some{ .. }) {
        panic!("Halt")
      };
      let mut res: ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput> = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      res = ::std::rc::Rc::new(super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
            value: input.value().clone()
          });
      output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>::Success {
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
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "SimpleStringImpl_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  #[derive(PartialEq, Clone)]
  pub enum Config {
    Config {}
  }
  impl Config {}
  impl ::dafny_runtime::DafnyPrint for Config {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Config::Config { } => {
          write!(_formatter, "SimpleStringImpl_Compile.Config.Config")?;
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
// SimpleString
pub mod r#_simple_dtypes_dsmithystring_dinternaldafny {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn DefaultSimpleStringConfig() -> super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::SimpleStringConfig {
      super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::SimpleStringConfig::SimpleStringConfig{}
    }
    /*method SimpleString(config: SimpleStringConfig)
    returns (res: Result<ISimpleTypesStringClient, Error>) {
        var client := new SimpleStringClient(Operations.Config);
        return Success(client);
    } */
    pub fn SimpleString(config: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::SimpleStringConfig>)
      -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<*mut dyn super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      let client: *mut SimpleStringClient = ::dafny_runtime::allocate::<SimpleStringClient>();
      SimpleStringClient::_ctor(client, &::std::rc::Rc::new(super::r#_SimpleStringImpl_Compile::Config::Config{}));
      let v = client as *mut dyn super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient;
      // build a success
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<*mut dyn super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>::Success{
          value: v
      })
    }
  }
  
  struct SimpleStringClient {
    r#_i_config: ::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>
  }

  impl SimpleStringClient {
    fn _ctor(this: *mut SimpleStringClient, config: &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>) {
      let mut _i_set_config = false;
      ::dafny_runtime::update_field_uninit!(this, r#_i_config, _i_set_config, config.clone());
    }
    fn config(&self) -> ::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config> {
      self.r#_i_config.clone()
    }
  }
  impl super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient for SimpleStringClient {
    fn GetString(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      super::r#_SimpleStringImpl_Compile::_default::GetString(&self.config(), input)
    }
    fn GetStringSingleValue(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      super::r#_SimpleStringImpl_Compile::_default::GetStringSingleValue(&self.config(), input)
    }
    fn GetStringUTF8(self: &Self, input: &::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>, ::std::rc::Rc<super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>>> {
      super::r#_SimpleStringImpl_Compile::_default::GetStringUTF8(&self.config(), input)
    }
  }
  ::dafny_runtime::UpcastTo!(SimpleStringClient, dyn super::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient);
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
    pub fn CreateStringSome(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
          value: s.clone()
        })
    }
    pub fn CreateStringNone() -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::None {})
    }
    pub fn CreateBooleanSome(b: bool) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {
          value: b
        })
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
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "StandardLibraryInterop_Compile.WrappersInterop")
    }
  }
  impl ::std::cmp::PartialEq for WrappersInterop {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
}
mod _module {
  
}