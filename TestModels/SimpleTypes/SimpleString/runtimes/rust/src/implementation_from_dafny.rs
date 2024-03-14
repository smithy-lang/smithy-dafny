#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
use dafny_runtime;
mod _System {
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct nat(pub ::dafny_runtime::BigInt);
  impl ::dafny_runtime::DafnyErasable for nat {
    type Erased = ::dafny_runtime::BigInt;
  }
  impl ::dafny_runtime::DafnyUnerasable<::dafny_runtime::BigInt> for nat {}
  impl ::dafny_runtime::DafnyUnerasable<nat> for nat {}
  impl ::std::default::Default for nat {
    fn default() -> Self {
      nat(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for nat {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for nat {
    type Target = ::dafny_runtime::BigInt;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(PartialEq)]
  pub enum Tuple2<T0,T1> {
    _T2 { _0: T0, _1: T1 },
    _PhantomVariant(::std::marker::PhantomData::<T0>, ::std::marker::PhantomData::<T1>)
  }
  impl <T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>Tuple2<T0,T1>
     where <T0 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <T1 as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
    pub fn _0(&self) -> &T0 {
      match self {
        Tuple2::_T2 { _0, _1, } => _0,
        Tuple2::_PhantomVariant(..) => panic!()
      }
    }
    pub fn _1(&self) -> &T1 {
      match self {
        Tuple2::_T2 { _0, _1, } => _1,
        Tuple2::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::dafny_runtime::DafnyErasable for Tuple2<T0,T1> {
    type Erased = Tuple2<T0::Erased, T1::Erased, >;
  }
  impl <T0__Erased, T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<T0__Erased> + 'static,T1__Erased, T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<T1__Erased> + 'static>::dafny_runtime::DafnyUnerasable<Tuple2<T0__Erased, T1__Erased, >> for Tuple2<T0,T1> {}
  impl <T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::dafny_runtime::DafnyPrint for Tuple2<T0,T1> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple2::_T2 { _0, _1, } => {
          write!(_formatter, "_System.Tuple2._T2(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(_0, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(_1, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Tuple2::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <T0: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T0> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,T1: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<T1> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::std::default::Default for Tuple2<T0,T1> {
    fn default() -> Self {
      Tuple2::_T2 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default()
      }
    }
  }
  #[derive(PartialEq)]
  pub enum Tuple0 {
    _T0 {}
  }
  impl Tuple0 {}
  impl ::dafny_runtime::DafnyErasable for Tuple0 {
    type Erased = Tuple0;
  }
  impl ::dafny_runtime::DafnyUnerasable<Tuple0> for Tuple0 {}
  impl ::dafny_runtime::DafnyPrint for Tuple0 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Tuple0::_T0 { } => {
          write!(_formatter, "_System.Tuple0._T0")?;
          Ok(())
        }
      }
    }
  }
  impl ::std::default::Default for Tuple0 {
    fn default() -> Self {
      Tuple0::_T0 {}
    }
  }
}
mod r#_SimpleTypesSmithyStringTypes_Compile {
  #[derive(PartialEq)]
  pub enum DafnyCallEvent<I,O> {
    DafnyCallEvent { input: I, output: O },
    _PhantomVariant(::std::marker::PhantomData::<I>, ::std::marker::PhantomData::<O>)
  }
  impl <I: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<I> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,O: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<O> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>DafnyCallEvent<I,O>
     where <I as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq, <O as ::dafny_runtime::DafnyErasable>::Erased: ::std::cmp::PartialEq,  {
    pub fn input(&self) -> &I {
      match self {
        DafnyCallEvent::DafnyCallEvent { input, output, } => input,
        DafnyCallEvent::_PhantomVariant(..) => panic!()
      }
    }
    pub fn output(&self) -> &O {
      match self {
        DafnyCallEvent::DafnyCallEvent { input, output, } => output,
        DafnyCallEvent::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <I: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<I> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,O: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<O> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::dafny_runtime::DafnyErasable for DafnyCallEvent<I,O> {
    type Erased = DafnyCallEvent<I::Erased, O::Erased, >;
  }
  impl <I__Erased, I: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<I> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<I__Erased> + 'static,O__Erased, O: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<O> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyUnerasable<O__Erased> + 'static>::dafny_runtime::DafnyUnerasable<DafnyCallEvent<I__Erased, O__Erased, >> for DafnyCallEvent<I,O> {}
  impl <I: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<I> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,O: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<O> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::dafny_runtime::DafnyPrint for DafnyCallEvent<I,O> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        DafnyCallEvent::DafnyCallEvent { input, output, } => {
          write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.DafnyCallEvent.DafnyCallEvent(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        DafnyCallEvent::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <I: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<I> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static,O: ::dafny_runtime::DafnyErasable + ::dafny_runtime::DafnyUnerasable<O> + Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>::std::default::Default for DafnyCallEvent<I,O> {
    fn default() -> Self {
      DafnyCallEvent::DafnyCallEvent {
        input: ::std::default::Default::default(),
        output: ::std::default::Default::default()
      }
    }
  }
  #[derive(PartialEq)]
  pub enum GetStringInput {
    GetStringInput { value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<Vec<char>>> }
  }
  impl GetStringInput {
    pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<Vec<char>>> {
      match self {
        GetStringInput::GetStringInput { value, } => value
      }
    }
  }
  impl ::dafny_runtime::DafnyErasable for GetStringInput {
    type Erased = GetStringInput;
  }
  impl ::dafny_runtime::DafnyUnerasable<GetStringInput> for GetStringInput {}
  impl ::dafny_runtime::DafnyPrint for GetStringInput {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        GetStringInput::GetStringInput { value, } => {
          write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.GetStringInput.GetStringInput(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        }
      }
    }
  }
  impl ::std::default::Default for GetStringInput {
    fn default() -> Self {
      GetStringInput::GetStringInput {
        value: ::std::default::Default::default()
      }
    }
  }
  #[derive(PartialEq)]
  pub enum GetStringOutput {
    GetStringOutput { value: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<Vec<char>>> }
  }
  impl GetStringOutput {
    pub fn value(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<Vec<char>>> {
      match self {
        GetStringOutput::GetStringOutput { value, } => value
      }
    }
  }
  impl ::dafny_runtime::DafnyErasable for GetStringOutput {
    type Erased = GetStringOutput;
  }
  impl ::dafny_runtime::DafnyUnerasable<GetStringOutput> for GetStringOutput {}
  impl ::dafny_runtime::DafnyPrint for GetStringOutput {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        GetStringOutput::GetStringOutput { value, } => {
          write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.GetStringOutput.GetStringOutput(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        }
      }
    }
  }
  impl ::std::default::Default for GetStringOutput {
    fn default() -> Self {
      GetStringOutput::GetStringOutput {
        value: ::std::default::Default::default()
      }
    }
  }
  #[derive(PartialEq)]
  pub enum SimpleStringConfig {
    SimpleStringConfig {}
  }
  impl SimpleStringConfig {}
  impl ::dafny_runtime::DafnyErasable for SimpleStringConfig {
    type Erased = SimpleStringConfig;
  }
  impl ::dafny_runtime::DafnyUnerasable<SimpleStringConfig> for SimpleStringConfig {}
  impl ::dafny_runtime::DafnyPrint for SimpleStringConfig {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        SimpleStringConfig::SimpleStringConfig { } => {
          write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.SimpleStringConfig.SimpleStringConfig")?;
          Ok(())
        }
      }
    }
  }
  impl ::std::default::Default for SimpleStringConfig {
    fn default() -> Self {
      SimpleStringConfig::SimpleStringConfig {}
    }
  }
  pub struct ISimpleTypesStringClientCallHistory {}
  impl ISimpleTypesStringClientCallHistory {
    pub fn new() -> Self {
      ISimpleTypesStringClientCallHistory {}
    }
  }
  impl ::std::default::Default for ISimpleTypesStringClientCallHistory {
    fn default() -> Self {
      ISimpleTypesStringClientCallHistory::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for ISimpleTypesStringClientCallHistory {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.ISimpleTypesStringClientCallHistory")
    }
  }
  impl ::std::cmp::PartialEq for ISimpleTypesStringClientCallHistory {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  impl ::dafny_runtime::DafnyErasable for ISimpleTypesStringClientCallHistory {
    type Erased = ISimpleTypesStringClientCallHistory;
  }
  impl ::dafny_runtime::DafnyUnerasable<ISimpleTypesStringClientCallHistory> for ISimpleTypesStringClientCallHistory {}
  #[derive(PartialEq)]
  pub enum Error {
    CollectionOfErrors { list: ::std::vec::Vec<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>, message: Vec<char> }
  }
  impl Error {
    pub fn list(&self) -> &::std::vec::Vec<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>> {
      match self {
        Error::CollectionOfErrors { list, message, } => list
      }
    }
    pub fn message(&self) -> &Vec<char> {
      match self {
        Error::CollectionOfErrors { list, message, } => message
      }
    }
  }
  impl ::dafny_runtime::DafnyErasable for Error {
    type Erased = Error;
  }
  impl ::dafny_runtime::DafnyUnerasable<Error> for Error {}
  impl ::dafny_runtime::DafnyPrint for Error {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Error::CollectionOfErrors { list, message, } => {
          write!(_formatter, "SimpleTypesSmithyStringTypes_Compile.Error.CollectionOfErrors(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(list, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        }
      }
    }
  }
  impl ::std::default::Default for Error {
    fn default() -> Self {
      Error::CollectionOfErrors {
        list: ::std::default::Default::default(),
        message: ::std::default::Default::default()
      }
    }
  }
}
mod r#_SimpleStringImpl_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn GetString(config:  &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      let mut r#__0_res: ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>;
      r#__0_res = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput::GetStringOutput {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(((input).value()).clone()))) })));
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Success {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&r#__0_res).clone()))) })));
      return (output);
      return (output);
    }
    pub fn GetStringSingleValue(config:  &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      if !(matches!((input).value().as_ref(), super::r#_Wrappers_Compile::Option::Some{ .. })) {
        panic!("Halt");
        } else {
        
        }
      if !((::dafny_runtime::DafnyErasable::erase_owned((((input).value()).value()).clone()) == ::dafny_runtime::DafnyErasable::erase_owned("TEST_SIMPLE_STRING_SINGLE_VALUE".chars().collect::<Vec<char>>()))) {
        panic!("Halt");
        } else {
        
        }
      let mut r#__1_res: ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>;
      r#__1_res = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput::GetStringOutput {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(((input).value()).clone()))) })));
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Success {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&r#__1_res).clone()))) })));
      return (output);
      return (output);
    }
    pub fn GetStringUTF8(config:  &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      if !(matches!((input).value().as_ref(), super::r#_Wrappers_Compile::Option::Some{ .. })) {
        panic!("Halt");
        } else {
        
        }
      let mut r#__2_res: ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>;
      r#__2_res = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput::GetStringOutput {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(((input).value()).clone()))) })));
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Success {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&r#__2_res).clone()))) })));
      return (output);
      return (output);
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
  impl ::dafny_runtime::DafnyErasable for _default {
    type Erased = _default;
  }
  impl ::dafny_runtime::DafnyUnerasable<_default> for _default {}
  #[derive(PartialEq)]
  pub enum Config {
    Config {}
  }
  impl Config {}
  impl ::dafny_runtime::DafnyErasable for Config {
    type Erased = Config;
  }
  impl ::dafny_runtime::DafnyUnerasable<Config> for Config {}
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
    fn default() -> Self {
      Config::Config {}
    }
  }
}
mod r#_SimpleString_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn DefaultSimpleStringConfig() -> ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::SimpleStringConfig> {
      ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_SimpleTypesSmithyStringTypes_Compile::SimpleStringConfig::SimpleStringConfig { })))
    }
    pub fn SimpleString(config:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::SimpleStringConfig>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut res: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>>;
      let mut r#__3_client: ::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>;
      let mut _nw0: ::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient> = <::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::std::rc::Rc::new(super::r#_SimpleString_Compile::SimpleStringClient::new()));
      ((&_nw0))._ctor(&::std::rc::Rc::new(super::r#_SimpleStringImpl_Compile::Config::Config { }));
      r#__3_client = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&_nw0).clone()));
      res = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Success {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&r#__3_client).clone()))) })));
      return (res);
      return (res);
    }
    pub fn CreateSuccessOfClient(client:  &::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Success {value: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(client.clone()))) })))
    }
    pub fn CreateFailureOfError(error:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::std::rc::Rc<super::r#_SimpleString_Compile::SimpleStringClient>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>::Failure {error: (::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(error.clone()))) })))
    }
  }
  impl ::std::default::Default for _default {
    fn default() -> Self {
      _default::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for _default {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "SimpleString_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  impl ::dafny_runtime::DafnyErasable for _default {
    type Erased = _default;
  }
  impl ::dafny_runtime::DafnyUnerasable<_default> for _default {}
  pub struct SimpleStringClient {
      pub _config: ::std::cell::RefCell<::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>>
    }
  impl SimpleStringClient {
    pub fn new() -> Self {
      SimpleStringClient {
        _config: ::std::cell::RefCell::new(<::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config> as std::default::Default>::default())
      }
    }
    pub fn _ctor(self: &::std::rc::Rc<Self>, config:  &::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config>) -> () {
      {
        let __rhs = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(config.clone()));
        *(self._config.borrow_mut()) = __rhs;
        }
      return ();
    }
    pub fn GetString(self: &::std::rc::Rc<Self>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      let mut _out0: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>>;
      _out0 = super::r#_SimpleStringImpl_Compile::_default::GetString(&(self).config(), input);
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&_out0).clone()));
      return (output);
    }
    pub fn GetStringSingleValue(self: &::std::rc::Rc<Self>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      let mut _out1: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>>;
      _out1 = super::r#_SimpleStringImpl_Compile::_default::GetStringSingleValue(&(self).config(), input);
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&_out1).clone()));
      return (output);
    }
    pub fn GetStringUTF8(self: &::std::rc::Rc<Self>, input:  &::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringInput>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> {
      let mut output: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> = <::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as ::dafny_runtime::DafnyUnerasable<_>>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned(<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>> as std::default::Default>::default()));
      let mut _out2: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::GetStringOutput>, ::std::rc::Rc<super::r#_SimpleTypesSmithyStringTypes_Compile::Error>>>;
      _out2 = super::r#_SimpleStringImpl_Compile::_default::GetStringUTF8(&(self).config(), input);
      output = ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((&_out2).clone()));
      return (output);
    }
    pub fn config(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_SimpleStringImpl_Compile::Config> {
      ::dafny_runtime::DafnyUnerasable::<_>::unerase_owned(::dafny_runtime::DafnyErasable::erase_owned((::std::ops::Deref::deref(&((self)._config.borrow()))).clone()))
    }
  }
  impl ::std::default::Default for SimpleStringClient {
    fn default() -> Self {
      SimpleStringClient::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for SimpleStringClient {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "SimpleString_Compile.SimpleStringClient")
    }
  }
  impl ::std::cmp::PartialEq for SimpleStringClient {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  impl ::dafny_runtime::DafnyErasable for SimpleStringClient {
    type Erased = SimpleStringClient;
  }
  impl ::dafny_runtime::DafnyUnerasable<SimpleStringClient> for SimpleStringClient {}
}
mod _module {
  
}