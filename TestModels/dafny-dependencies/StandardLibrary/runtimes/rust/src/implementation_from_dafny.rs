#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
extern crate dafny_runtime;
mod _System {
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct nat(pub ::dafny_runtime::DafnyInt);
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
    type Target = ::dafny_runtime::DafnyInt;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(PartialEq)]
  pub enum Tuple2<T0, T1> {
    _T2 { _0: T0, _1: T1 },
    _PhantomVariant(::std::marker::PhantomData::<T0>, ::std::marker::PhantomData::<T1>)
  }
  impl <T0: Clone + ::dafny_runtime::DafnyPrint + 'static, T1: Clone + ::dafny_runtime::DafnyPrint + 'static>Tuple2<T0, T1> {
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
  impl <T0: Clone + ::dafny_runtime::DafnyPrint + 'static, T1: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for Tuple2<T0, T1> {
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
  impl <T0: ::std::default::Default, T1: ::std::default::Default>::std::default::Default for Tuple2<T0, T1> {
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
mod r#_Wrappers_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn Need<_E: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(condition: &bool, error: &_E) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Outcome<_E>>
       where  {
      if condition.clone() {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Outcome::<_E>::Pass { })
      } else {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Outcome::<_E>::Fail {error: (error.clone()) })
      }
    }
  }
  impl ::std::default::Default for _default {
    fn default() -> Self {
      _default::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for _default {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "Wrappers_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  #[derive(PartialEq)]
  pub enum Option<T> {
    None {},
    Some { value: T },
    _PhantomVariant(::std::marker::PhantomData::<T>)
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>Option<T> {
    pub fn ToResult(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      let mut _source0: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> = (self).clone();
      if matches!(&_source0.as_ref(), super::r#_Wrappers_Compile::Option::None{ .. }) {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Failure {error: (::dafny_runtime::string_of("Option is None")) })
      } else {
        let mut r#___mcc_h0: T = (&_source0).value();
        let mut v: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Success {value: (v.clone()) })
      }
    }
    pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
      let mut _source1: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> = (self).clone();
      if matches!(&_source1.as_ref(), super::r#_Wrappers_Compile::Option::None{ .. }) {
        default.clone()
      } else {
        let mut r#___mcc_h0: T = (&_source1).value();
        let mut v: T = r#___mcc_h0.clone();
        v.clone()
      }
    }
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Option::None{ .. })
    }
    pub fn PropagateFailure<_U: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<_U>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<_U>::None { })
    }
    pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
      (self).value()
    }
    pub fn value(&self) -> &T {
      match self {
        Option::None { } => panic!("field does not exist on this variant"),
        Option::Some { value, } => value,
        Option::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for Option<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Option::None { } => {
          write!(_formatter, "Wrappers_Compile.Option.None")?;
          Ok(())
        },
        Option::Some { value, } => {
          write!(_formatter, "Wrappers_Compile.Option.Some(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Option::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <T: ::std::default::Default>::std::default::Default for Option<T> {
    fn default() -> Self {
      Option::None {}
    }
  }
  #[derive(PartialEq)]
  pub enum Result<T, R> {
    Success { value: T },
    Failure { error: R },
    _PhantomVariant(::std::marker::PhantomData::<T>, ::std::marker::PhantomData::<R>)
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static, R: Clone + ::dafny_runtime::DafnyPrint + 'static>Result<T, R> {
    pub fn ToOption(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> {
      let mut _source2: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = (self).clone();
      if matches!(&_source2.as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = (&_source2).value();
        let mut s: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<T>::Some {value: (s.clone()) })
      } else {
        let mut r#___mcc_h1: R = (&_source2).error();
        let mut e: R = r#___mcc_h1.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<T>::None { })
      }
    }
    pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
      let mut _source3: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = (self).clone();
      if matches!(&_source3.as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = (&_source3).value();
        let mut s: T = r#___mcc_h0.clone();
        s.clone()
      } else {
        let mut r#___mcc_h1: R = (&_source3).error();
        let mut e: R = r#___mcc_h1.clone();
        default.clone()
      }
    }
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Result::Failure{ .. })
    }
    pub fn PropagateFailure<_U: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<_U, R>::Failure {error: ((self).error()) })
    }
    pub fn MapFailure<_NewR: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>, reWrap: &::dafny_runtime::FunctionWrapper<dyn ::std::ops::Fn(&R) -> _NewR + 'static>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, _NewR>>
       where  {
      let mut _source4: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = (self).clone();
      if matches!(&_source4.as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = (&_source4).value();
        let mut s: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, _NewR>::Success {value: (s.clone()) })
      } else {
        let mut r#___mcc_h1: R = (&_source4).error();
        let mut e: R = r#___mcc_h1.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, _NewR>::Failure {error: (((reWrap).0(&e))) })
      }
    }
    pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
      (self).value()
    }
    pub fn value(&self) -> &T {
      match self {
        Result::Success { value, } => value,
        Result::Failure { error, } => panic!("field does not exist on this variant"),
        Result::_PhantomVariant(..) => panic!()
      }
    }
    pub fn error(&self) -> &R {
      match self {
        Result::Success { value, } => panic!("field does not exist on this variant"),
        Result::Failure { error, } => error,
        Result::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static, R: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for Result<T, R> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Result::Success { value, } => {
          write!(_formatter, "Wrappers_Compile.Result.Success(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Result::Failure { error, } => {
          write!(_formatter, "Wrappers_Compile.Result.Failure(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(error, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Result::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <T: ::std::default::Default, R: ::std::default::Default>::std::default::Default for Result<T, R> {
    fn default() -> Self {
      Result::Success {
        value: ::std::default::Default::default()
      }
    }
  }
  #[derive(PartialEq)]
  pub enum Outcome<E> {
    Pass {},
    Fail { error: E },
    _PhantomVariant(::std::marker::PhantomData::<E>)
  }
  impl <E: Clone + ::dafny_runtime::DafnyPrint + 'static>Outcome<E> {
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Outcome::Fail{ .. })
    }
    pub fn PropagateFailure<_U: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, E>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<_U, E>::Failure {error: ((self).error()) })
    }
    pub fn error(&self) -> &E {
      match self {
        Outcome::Pass { } => panic!("field does not exist on this variant"),
        Outcome::Fail { error, } => error,
        Outcome::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <E: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for Outcome<E> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      match self {
        Outcome::Pass { } => {
          write!(_formatter, "Wrappers_Compile.Outcome.Pass")?;
          Ok(())
        },
        Outcome::Fail { error, } => {
          write!(_formatter, "Wrappers_Compile.Outcome.Fail(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(error, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
        Outcome::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <E: ::std::default::Default>::std::default::Default for Outcome<E> {
    fn default() -> Self {
      Outcome::Pass {}
    }
  }
}
mod r#_StandardLibrary_Compile_dUInt_Compile {
  use dafny_runtime::ToPrimitive;
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn UInt8Less(a: &u8, b: &u8) -> bool {
      a.clone() < b.clone()
    }
    pub fn HasUint16Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {          
      s.cardinality() < (&(<(super::r#_StandardLibrary_Compile_dUInt_Compile::_default)>::UINT16_LIMIT))
    }
    pub fn HasUint32Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {
      s.cardinality() < (&(<(super::r#_StandardLibrary_Compile_dUInt_Compile::_default)>::UINT32_LIMIT))
    }
    pub fn HasUint64Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {
      s.cardinality() < (&(<(super::r#_StandardLibrary_Compile_dUInt_Compile::_default)>::UINT64_LIMIT))
    }
    pub fn UInt16ToSeq(x: &u16) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = ToPrimitive::to_u8(x.clone() / (/*optimized*/256)).unwrap();
      let mut b1: u8 = ToPrimitive::to_u8(x.clone() % (/*optimized*/256)).unwrap();
      ::dafny_runtime::seq![b0.clone(), b1.clone()]
    }
    pub fn SeqToUInt16(s: &::dafny_runtime::Sequence<u8>) -> u16 {
      let mut x0: u16 = (ToPrimitive::to_u16(s.get(&::dafny_runtime::DafnyInt::from(0))).unwrap()) * (/*optimized*/256);
      x0.clone() + (ToPrimitive::to_u16(s.get(&::dafny_runtime::DafnyInt::from(1))).unwrap())
    }
    pub fn UInt32ToSeq(x: &u32) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = ToPrimitive::to_u8(x.clone() / (/*optimized*/16777216)).unwrap();
      let mut x0: u32 = x.clone() - (ToPrimitive::to_u32(b0.clone()).unwrap()) * (/*optimized*/16777216);
      let mut b1: u8 = ToPrimitive::to_u8(x0.clone() / (/*optimized*/65536)).unwrap();
      let mut x1: u32 = x0.clone() - (ToPrimitive::to_u32(b1.clone()).unwrap()) * (/*optimized*/65536);
      let mut b2: u8 = ToPrimitive::to_u8(x1.clone() / (/*optimized*/256)).unwrap();
      let mut b3: u8 = ToPrimitive::to_u8(x1.clone() % (/*optimized*/256)).unwrap();
      ::dafny_runtime::seq![b0.clone(), b1.clone(), b2.clone(), b3.clone()]
    }
    pub fn SeqToUInt32(s: &::dafny_runtime::Sequence<u8>) -> u32 {
      let mut x0: u32 = (ToPrimitive::to_u32(s.get(&::dafny_runtime::DafnyInt::from(0))).unwrap()) * (/*optimized*/16777216);
      let mut x1: u32 = x0.clone() + (ToPrimitive::to_u32(s.get(&::dafny_runtime::DafnyInt::from(1))).unwrap()) * (/*optimized*/65536);
      let mut x2: u32 = x1.clone() + (ToPrimitive::to_u32(s.get(&::dafny_runtime::DafnyInt::from(2))).unwrap()) * (/*optimized*/256);
      x2.clone() + (ToPrimitive::to_u32(s.get(&::dafny_runtime::DafnyInt::from(3))).unwrap())
    }
    pub fn UInt64ToSeq(x: &u64) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = ToPrimitive::to_u8(x.clone() / (/*optimized*/72057594037927936)).unwrap();
      let mut x0: u64 = x.clone() - (ToPrimitive::to_u64(b0.clone()).unwrap()) * (/*optimized*/72057594037927936);
      let mut b1: u8 = ToPrimitive::to_u8(x0.clone() / (/*optimized*/281474976710656)).unwrap();
      let mut x1: u64 = x0.clone() - (ToPrimitive::to_u64(b1.clone()).unwrap()) * (/*optimized*/281474976710656);
      let mut b2: u8 = ToPrimitive::to_u8(x1.clone() / (/*optimized*/1099511627776)).unwrap();
      let mut x2: u64 = x1.clone() - (ToPrimitive::to_u64(b2.clone()).unwrap()) * (/*optimized*/1099511627776);
      let mut b3: u8 = ToPrimitive::to_u8(x2.clone() / (/*optimized*/4294967296)).unwrap();
      let mut x3: u64 = x2.clone() - (ToPrimitive::to_u64(b3.clone()).unwrap()) * (/*optimized*/4294967296);
      let mut b4: u8 = ToPrimitive::to_u8(x3.clone() / (/*optimized*/16777216)).unwrap();
      let mut x4: u64 = x3.clone() - (ToPrimitive::to_u64(b4.clone()).unwrap()) * (/*optimized*/16777216);
      let mut b5: u8 = ToPrimitive::to_u8(x4.clone() / (/*optimized*/65536)).unwrap();
      let mut x5: u64 = x4.clone() - (ToPrimitive::to_u64(b5.clone()).unwrap()) * (/*optimized*/65536);
      let mut b6: u8 = ToPrimitive::to_u8(x5.clone() / (/*optimized*/256)).unwrap();
      let mut b7: u8 = ToPrimitive::to_u8(x5.clone() % (/*optimized*/256)).unwrap();
      ::dafny_runtime::seq![b0.clone(), b1.clone(), b2.clone(), b3.clone(), b4.clone(), b5.clone(), b6.clone(), b7.clone()]
    }
    pub fn SeqToUInt64(s: &::dafny_runtime::Sequence<u8>) -> u64 {
      let mut x0: u64 = (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(0))).unwrap()) * (/*optimized*/72057594037927936);
      let mut x1: u64 = x0.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(1))).unwrap()) * (/*optimized*/281474976710656);
      let mut x2: u64 = x1.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(2))).unwrap()) * (/*optimized*/1099511627776);
      let mut x3: u64 = x2.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(3))).unwrap()) * (/*optimized*/4294967296);
      let mut x4: u64 = x3.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(4))).unwrap()) * (/*optimized*/16777216);
      let mut x5: u64 = x4.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(5))).unwrap()) * (/*optimized*/65536);
      let mut x6: u64 = x5.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(6))).unwrap()) * (/*optimized*/256);
      let mut x: u64 = x6.clone() + (ToPrimitive::to_u64(s.get(&::dafny_runtime::DafnyInt::from(7))).unwrap());
      x.clone()
    }
    pub fn UINT16_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::DafnyInt::from(b"65536")
    }
    pub fn UINT32_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::DafnyInt::from(b"4294967296")
    }
    pub fn UINT64_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::DafnyInt::from(b"18446744073709551616")
    }
    pub fn INT32_MAX_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::DafnyInt::from(b"2147483648")
    }
    pub fn INT64_MAX_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::DafnyInt::from(b"9223372036854775808")
    }
  }
  impl ::std::default::Default for _default {
    fn default() -> Self {
      _default::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for _default {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "StandardLibrary_Compile.UInt_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct uint8(pub u8);
  impl ::std::default::Default for uint8 {
    fn default() -> Self {
      uint8(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for uint8 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for uint8 {
    type Target = u8;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct uint16(pub u16);
  impl ::std::default::Default for uint16 {
    fn default() -> Self {
      uint16(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for uint16 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for uint16 {
    type Target = u16;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct uint32(pub u32);
  impl ::std::default::Default for uint32 {
    fn default() -> Self {
      uint32(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for uint32 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for uint32 {
    type Target = u32;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct uint64(pub u64);
  impl ::std::default::Default for uint64 {
    fn default() -> Self {
      uint64(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for uint64 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for uint64 {
    type Target = u64;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct int32(pub i32);
  impl ::std::default::Default for int32 {
    fn default() -> Self {
      int32(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for int32 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for int32 {
    type Target = i32;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct int64(pub i64);
  impl ::std::default::Default for int64 {
    fn default() -> Self {
      int64(::std::default::Default::default())
    }
  }
  impl ::dafny_runtime::DafnyPrint for int64 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for int64 {
    type Target = i64;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct posInt64(pub u64);
  impl ::std::default::Default for posInt64 {
    fn default() -> Self {
      posInt64(::dafny_runtime::DafnyInt::from(1))
      
    }
  }
  impl ::dafny_runtime::DafnyPrint for posInt64 {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for posInt64 {
    type Target = u64;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct seq16<T>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::default::Default for seq16<T> {
    fn default() -> Self {
      seq16(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for seq16<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::ops::Deref for seq16<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct seq32<T>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::default::Default for seq32<T> {
    fn default() -> Self {
      seq32(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for seq32<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::ops::Deref for seq32<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct seq64<T>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::default::Default for seq64<T> {
    fn default() -> Self {
      seq64(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::dafny_runtime::DafnyPrint for seq64<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + 'static>::std::ops::Deref for seq64<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
}
mod r#_StandardLibrary_Compile {
  
}
mod r#_UTF8_Compile {
  use dafny_runtime::ToPrimitive;
  use dafny_runtime::BigInt;
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn Encode(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Failure {error: (::dafny_runtime::string_of("")) })
    }
    pub fn Decode(b: &::dafny_runtime::Sequence<u8>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Failure {error: (::dafny_runtime::string_of("")) })
    }
    pub fn CreateEncodeSuccess(bytes: &super::r#_UTF8_Compile::ValidUTF8Bytes) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Success {value: (bytes.clone()) })
    }
    pub fn CreateEncodeFailure(error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Failure {error: (error.clone()) })
    }
    pub fn CreateDecodeSuccess(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Success {value: (s.clone()) })
    }
    pub fn CreateDecodeFailure(error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Failure {error: (error.clone()) })
    }
    pub fn IsASCIIString(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> bool {
      true
    }
    pub fn EncodeAscii(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> super::r#_UTF8_Compile::ValidUTF8Bytes {
      let mut _accumulator: super::r#_UTF8_Compile::ValidUTF8Bytes = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>;
      let mut s = s.clone();
      'TAIL_CALL_START: loop {
        if s.cardinality() == ::dafny_runtime::DafnyInt::from(0) {
          return _accumulator.concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>));
        } else {
          let mut x: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![ToPrimitive::to_u8(::dafny_runtime::DafnyInt{data: BigInt::from(s.get(&::dafny_runtime::DafnyInt::from(0)) as u32)}).unwrap()];
          _accumulator = _accumulator.concat(&x);
          let mut _in0: ::dafny_runtime::Sequence<::dafny_runtime::DafnyChar> = s.drop(&::dafny_runtime::DafnyInt::from(1));
          s = _in0.clone();
          continue 'TAIL_CALL_START;
        }
      }
    }
    pub fn Uses1Byte(s: &::dafny_runtime::Sequence<u8>) -> bool {
      (/*optimized*/0) <= s.get(&::dafny_runtime::DafnyInt::from(0)) && s.get(&::dafny_runtime::DafnyInt::from(0)) <= (/*optimized*/127)
    }
    pub fn Uses2Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
      (/*optimized*/194) <= s.get(&::dafny_runtime::DafnyInt::from(0)) && s.get(&::dafny_runtime::DafnyInt::from(0)) <= (/*optimized*/223) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191))
    }
    pub fn Uses3Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
      s.get(&::dafny_runtime::DafnyInt::from(0)) == (/*optimized*/224) && ((/*optimized*/160) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) || (/*optimized*/225) <= s.get(&::dafny_runtime::DafnyInt::from(0)) && s.get(&::dafny_runtime::DafnyInt::from(0)) <= (/*optimized*/236) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) || s.get(&::dafny_runtime::DafnyInt::from(0)) == (/*optimized*/237) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/159)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) || (/*optimized*/238) <= s.get(&::dafny_runtime::DafnyInt::from(0)) && s.get(&::dafny_runtime::DafnyInt::from(0)) <= (/*optimized*/239) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191))
    }
    pub fn Uses4Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
      s.get(&::dafny_runtime::DafnyInt::from(0)) == (/*optimized*/240) && ((/*optimized*/144) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(3)) && s.get(&::dafny_runtime::DafnyInt::from(3)) <= (/*optimized*/191)) || (/*optimized*/241) <= s.get(&::dafny_runtime::DafnyInt::from(0)) && s.get(&::dafny_runtime::DafnyInt::from(0)) <= (/*optimized*/243) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(3)) && s.get(&::dafny_runtime::DafnyInt::from(3)) <= (/*optimized*/191)) || s.get(&::dafny_runtime::DafnyInt::from(0)) == (/*optimized*/244) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(1)) && s.get(&::dafny_runtime::DafnyInt::from(1)) <= (/*optimized*/143)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(2)) && s.get(&::dafny_runtime::DafnyInt::from(2)) <= (/*optimized*/191)) && ((/*optimized*/128) <= s.get(&::dafny_runtime::DafnyInt::from(3)) && s.get(&::dafny_runtime::DafnyInt::from(3)) <= (/*optimized*/191))
    }
    pub fn ValidUTF8Range(a: &::dafny_runtime::Sequence<u8>, lo: &super::_System::nat, hi: &super::_System::nat) -> bool {
      let mut a = a.clone();
      let mut lo = lo.clone();
      let mut hi = hi.clone();
      'TAIL_CALL_START: loop {
        if lo.clone() == hi.clone() {
          return true;
        } else {
          let mut r: ::dafny_runtime::Sequence<u8> = a.slice(&lo, &hi);
          if <(super::r#_UTF8_Compile::_default)>::Uses1Byte {
            let mut _in1: ::dafny_runtime::Sequence<u8> = a.clone();
            let mut _in2: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(1);
            let mut _in3: super::_System::nat = hi.clone();
            a = _in1.clone();
            lo = _in2.clone();
            hi = _in3.clone();
            continue 'TAIL_CALL_START;
          } else {
            if ::dafny_runtime::DafnyInt::from(2) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses2Bytes {
              let mut _in4: ::dafny_runtime::Sequence<u8> = a.clone();
              let mut _in5: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(2);
              let mut _in6: super::_System::nat = hi.clone();
              a = _in4.clone();
              lo = _in5.clone();
              hi = _in6.clone();
              continue 'TAIL_CALL_START;
            } else {
              if ::dafny_runtime::DafnyInt::from(3) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses3Bytes {
                let mut _in7: ::dafny_runtime::Sequence<u8> = a.clone();
                let mut _in8: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(3);
                let mut _in9: super::_System::nat = hi.clone();
                a = _in7.clone();
                lo = _in8.clone();
                hi = _in9.clone();
                continue 'TAIL_CALL_START;
              } else {
                if ::dafny_runtime::DafnyInt::from(4) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses4Bytes {
                  let mut _in10: ::dafny_runtime::Sequence<u8> = a.clone();
                  let mut _in11: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(4);
                  let mut _in12: super::_System::nat = hi.clone();
                  a = _in10.clone();
                  lo = _in11.clone();
                  hi = _in12.clone();
                  continue 'TAIL_CALL_START;
                } else {
                  return false;
                }
              }
            }
          }
        }
      }
    }
    pub fn ValidUTF8Seq(s: &::dafny_runtime::Sequence<u8>) -> bool {
      <(super::r#_UTF8_Compile::_default)>::ValidUTF8Range(s, &::dafny_runtime::DafnyInt::from(0), &s.cardinality())
    }
  }
  impl ::std::default::Default for _default {
    fn default() -> Self {
      _default::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for _default {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "UTF8_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct ValidUTF8Bytes(pub ::dafny_runtime::Sequence<u8>);
  impl ::std::default::Default for ValidUTF8Bytes {
    fn default() -> Self {
      ValidUTF8Bytes(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>)
      
    }
  }
  impl ::dafny_runtime::DafnyPrint for ValidUTF8Bytes {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl ::std::ops::Deref for ValidUTF8Bytes {
    type Target = ::dafny_runtime::Sequence<u8>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
}
mod r#_StandardLibraryInterop_Compile {
  pub struct WrappersInterop {}
  impl WrappersInterop {
    pub fn new() -> Self {
      WrappersInterop {}
    }
    pub fn CreateStringSome(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::Some {value: (s.clone()) })
    }
    pub fn CreateStringNone() -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyChar>>::None { })
    }
    pub fn CreateBooleanSome(b: &bool) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::Some {value: (b.clone()) })
    }
    pub fn CreateBooleanNone() -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None { })
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