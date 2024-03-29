#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
extern crate dafny_runtime;
pub mod _System {
  pub trait object {}
  pub type nat = ::dafny_runtime::DafnyInt;
  #[derive(PartialEq, Clone)]
  pub enum Tuple2<T0, T1> {
    _T2 { _0: T0, _1: T1 },
    _PhantomVariant(::std::marker::PhantomData::<T0>, ::std::marker::PhantomData::<T1>)
  }
  impl <T0: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static, T1: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>Tuple2<T0, T1> {
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
  impl <T0: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static, T1: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::dafny_runtime::DafnyPrint for Tuple2<T0, T1> {
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
    fn default() -> Tuple2<T0, T1> {
      Tuple2::_T2 {
        _0: ::std::default::Default::default(),
        _1: ::std::default::Default::default()
      }
    }
  }
  impl <T0: ::std::default::Default, T1: ::std::default::Default>::std::convert::AsRef<Tuple2<T0, T1>> for &Tuple2<T0, T1> {
    fn as_ref(&self) -> Self {
      self
    }
  }
  #[derive(PartialEq, Clone)]
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
    fn default() -> Tuple0 {
      Tuple0::_T0 {}
    }
  }
  impl ::std::convert::AsRef<Tuple0> for &Tuple0 {
    fn as_ref(&self) -> Self {
      self
    }
  }
}
pub mod r#_Wrappers_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn _allocated() -> *mut Self {
      ::dafny_runtime::allocate::<Self>()
    }
    pub fn Need<_E: ::dafny_runtime::DafnyType + ::std::default::Default + 'static>(condition: bool, error: &_E) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Outcome<_E>>
       where  {
      if condition {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Outcome::<_E>::Pass {})
      } else {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Outcome::<_E>::Fail {
            error: error.clone()
          })
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
  #[derive(PartialEq, Clone)]
  pub enum Option<T> {
    None {},
    Some { value: T },
    _PhantomVariant(::std::marker::PhantomData::<T>)
  }
  impl <T: ::dafny_runtime::DafnyTypeEq + 'static>Option<T> {
    pub fn ToResult(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      let mut _source0: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> = self.clone();
      if matches!((&_source0).as_ref(), super::r#_Wrappers_Compile::Option::None{ .. }) {
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Failure {
            error: ::dafny_runtime::string_utf16_of("Option is None")
          })
      } else {
        let mut r#___mcc_h0: T = _source0.value().clone();
        let mut v: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Success {
            value: v.clone()
          })
      }
    }
    pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
      let mut _source1: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> = self.clone();
      if matches!((&_source1).as_ref(), super::r#_Wrappers_Compile::Option::None{ .. }) {
        default.clone()
      } else {
        let mut r#___mcc_h0: T = _source1.value().clone();
        let mut v: T = r#___mcc_h0.clone();
        v.clone()
      }
    }
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Option::None{ .. })
    }
    pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<_U>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<_U>::None {})
    }
    pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
      self.value().clone()
    }
    pub fn value(&self) -> &T {
      match self {
        Option::None { } => panic!("field does not exist on this variant"),
        Option::Some { value, } => value,
        Option::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <T: ::dafny_runtime::DafnyType + 'static>::dafny_runtime::DafnyPrint for Option<T> {
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
    fn default() -> Option<T> {
      Option::None {}
    }
  }
  impl <T: ::std::default::Default>::std::convert::AsRef<Option<T>> for &Option<T> {
    fn as_ref(&self) -> Self {
      self
    }
  }
  impl <T: ::dafny_runtime::DafnyTypeEq + 'static> core::fmt::Debug for Option<T> {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
    }
  }
  impl <T: ::dafny_runtime::DafnyTypeEq + 'static> ::dafny_runtime::DafnyType for Option<T> {}
  impl <T: ::dafny_runtime::DafnyTypeEq> Eq for Option<T> {}
  impl <T: ::dafny_runtime::DafnyTypeEq> std::hash::Hash for Option<T> {
    fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
      match self {
        Option::None { } => {
        },
        Option::Some { value, } => {
          value.hash(state);
        },
        Option::_PhantomVariant(..) => {panic!()}
      }
    }
  }
  impl <T: ::dafny_runtime::DafnyTypeEq + 'static> ::dafny_runtime::DafnyTypeEq for Option<T> {}
  #[derive(PartialEq, Clone, Debug)]
  pub enum Result<T, R> {
    Success { value: T },
    Failure { error: R },
    _PhantomVariant(::std::marker::PhantomData::<T>, ::std::marker::PhantomData::<R>)
  }
  impl <T: ::dafny_runtime::DafnyType + 'static, R: ::dafny_runtime::DafnyType + 'static>Result<T, R> {
    pub fn ToOption(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<T>> {
      let mut _source2: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = self.clone();
      if matches!((&_source2).as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = _source2.value().clone();
        let mut s: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<T>::Some {
            value: s.clone()
          })
      } else {
        let mut r#___mcc_h1: R = _source2.error().clone();
        let mut e: R = r#___mcc_h1.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<T>::None {})
      }
    }
    pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
      let mut _source3: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = self.clone();
      if matches!((&_source3).as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = _source3.value().clone();
        let mut s: T = r#___mcc_h0.clone();
        s.clone()
      } else {
        let mut r#___mcc_h1: R = _source3.error().clone();
        let mut e: R = r#___mcc_h1.clone();
        default.clone()
      }
    }
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Result::Failure{ .. })
    }
    pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, R>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<_U, R>::Failure {
          error: self.error().clone()
        })
    }
    pub fn MapFailure<_NewR: ::dafny_runtime::DafnyType + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>, reWrap: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&R) -> _NewR + 'static>>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, _NewR>>
       where  {
      let mut _source4: ::std::rc::Rc<super::r#_Wrappers_Compile::Result<T, R>> = self.clone();
      if matches!((&_source4).as_ref(), super::r#_Wrappers_Compile::Result::Success{ .. }) {
        let mut r#___mcc_h0: T = _source4.value().clone();
        let mut s: T = r#___mcc_h0.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, _NewR>::Success {
            value: s.clone()
          })
      } else {
        let mut r#___mcc_h1: R = _source4.error().clone();
        let mut e: R = r#___mcc_h1.clone();
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<T, _NewR>::Failure {
            error: ((reWrap).0(&e))
          })
      }
    }
    pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
      self.value().clone()
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
  impl <T: ::dafny_runtime::DafnyType + 'static, R: ::dafny_runtime::DafnyType + 'static>::dafny_runtime::DafnyPrint for Result<T, R> {
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
    fn default() -> Result<T, R> {
      Result::Success {
        value: ::std::default::Default::default()
      }
    }
  }
  impl <T: ::std::default::Default, R: ::std::default::Default>::std::convert::AsRef<Result<T, R>> for &Result<T, R> {
    fn as_ref(&self) -> Self {
      self
    }
  }
  impl <T: ::dafny_runtime::DafnyType + 'static, R: ::dafny_runtime::DafnyType + 'static> ::dafny_runtime::DafnyType for Result<T, R> {}
  #[derive(PartialEq, Clone)]
  pub enum Outcome<E> {
    Pass {},
    Fail { error: E },
    _PhantomVariant(::std::marker::PhantomData::<E>)
  }
  impl <E: ::dafny_runtime::DafnyType + 'static>Outcome<E> {
    pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
      matches!(self.as_ref(), super::r#_Wrappers_Compile::Outcome::Fail{ .. })
    }
    pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType + ::std::default::Default + 'static>(self: &::std::rc::Rc<Self>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<_U, E>>
       where  {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<_U, E>::Failure {
          error: self.error().clone()
        })
    }
    pub fn error(&self) -> &E {
      match self {
        Outcome::Pass { } => panic!("field does not exist on this variant"),
        Outcome::Fail { error, } => error,
        Outcome::_PhantomVariant(..) => panic!()
      }
    }
  }
  impl <E: ::dafny_runtime::DafnyType + 'static>::dafny_runtime::DafnyPrint for Outcome<E> {
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
    fn default() -> Outcome<E> {
      Outcome::Pass {}
    }
  }
  impl <E: ::std::default::Default>::std::convert::AsRef<Outcome<E>> for &Outcome<E> {
    fn as_ref(&self) -> Self {
      self
    }
  }
}
pub mod r#_StandardLibrary_Compile_dUInt_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn _allocated() -> *mut Self {
      ::dafny_runtime::allocate::<Self>()
    }
    pub fn UInt8Less(a: u8, b: u8) -> bool {
      a < b
    }
    pub fn HasUint16Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {
      s.cardinality() < super::r#_StandardLibrary_Compile_dUInt_Compile::_default::UINT16_LIMIT()
    }
    pub fn HasUint32Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {
      s.cardinality() < super::r#_StandardLibrary_Compile_dUInt_Compile::_default::UINT32_LIMIT()
    }
    pub fn HasUint64Len<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>) -> bool
       where  {
      s.cardinality() < super::r#_StandardLibrary_Compile_dUInt_Compile::_default::UINT64_LIMIT()
    }
    pub fn UInt16ToSeq(x: u16) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = (x / 256) as u8;
      let mut b1: u8 = (x % 256) as u8;
      ::dafny_runtime::seq![b0, b1]
    }
    pub fn SeqToUInt16(s: &::dafny_runtime::Sequence<u8>) -> u16 {
      let mut x0: u16 = s.get(&::dafny_runtime::int!(0)) as u16 * 256;
      x0 + s.get(&::dafny_runtime::int!(1)) as u16
    }
    pub fn UInt32ToSeq(x: u32) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = (x / 16777216) as u8;
      let mut x0: u32 = x - b0 as u32 * 16777216;
      let mut b1: u8 = (x0 / 65536) as u8;
      let mut x1: u32 = x0 - b1 as u32 * 65536;
      let mut b2: u8 = (x1 / 256) as u8;
      let mut b3: u8 = (x1 % 256) as u8;
      ::dafny_runtime::seq![b0, b1, b2, b3]
    }
    pub fn SeqToUInt32(s: &::dafny_runtime::Sequence<u8>) -> u32 {
      let mut x0: u32 = s.get(&::dafny_runtime::int!(0)) as u32 * 16777216;
      let mut x1: u32 = x0 + s.get(&::dafny_runtime::int!(1)) as u32 * 65536;
      let mut x2: u32 = x1 + s.get(&::dafny_runtime::int!(2)) as u32 * 256;
      x2 + s.get(&::dafny_runtime::int!(3)) as u32
    }
    pub fn UInt64ToSeq(x: u64) -> ::dafny_runtime::Sequence<u8> {
      let mut b0: u8 = (x / 72057594037927936) as u8;
      let mut x0: u64 = x - b0 as u64 * 72057594037927936;
      let mut b1: u8 = (x0 / 281474976710656) as u8;
      let mut x1: u64 = x0 - b1 as u64 * 281474976710656;
      let mut b2: u8 = (x1 / 1099511627776) as u8;
      let mut x2: u64 = x1 - b2 as u64 * 1099511627776;
      let mut b3: u8 = (x2 / 4294967296) as u8;
      let mut x3: u64 = x2 - b3 as u64 * 4294967296;
      let mut b4: u8 = (x3 / 16777216) as u8;
      let mut x4: u64 = x3 - b4 as u64 * 16777216;
      let mut b5: u8 = (x4 / 65536) as u8;
      let mut x5: u64 = x4 - b5 as u64 * 65536;
      let mut b6: u8 = (x5 / 256) as u8;
      let mut b7: u8 = (x5 % 256) as u8;
      ::dafny_runtime::seq![b0, b1, b2, b3, b4, b5, b6, b7]
    }
    pub fn SeqToUInt64(s: &::dafny_runtime::Sequence<u8>) -> u64 {
      let mut x0: u64 = s.get(&::dafny_runtime::int!(0)) as u64 * 72057594037927936;
      let mut x1: u64 = x0 + s.get(&::dafny_runtime::int!(1)) as u64 * 281474976710656;
      let mut x2: u64 = x1 + s.get(&::dafny_runtime::int!(2)) as u64 * 1099511627776;
      let mut x3: u64 = x2 + s.get(&::dafny_runtime::int!(3)) as u64 * 4294967296;
      let mut x4: u64 = x3 + s.get(&::dafny_runtime::int!(4)) as u64 * 16777216;
      let mut x5: u64 = x4 + s.get(&::dafny_runtime::int!(5)) as u64 * 65536;
      let mut x6: u64 = x5 + s.get(&::dafny_runtime::int!(6)) as u64 * 256;
      let mut x: u64 = x6 + s.get(&::dafny_runtime::int!(7)) as u64;
      x
    }
    pub fn UINT16_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::int!(b"65536")
    }
    pub fn UINT32_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::int!(b"4294967296")
    }
    pub fn UINT64_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::int!(b"18446744073709551616")
    }
    pub fn INT32_MAX_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::int!(b"2147483648")
    }
    pub fn INT64_MAX_LIMIT() -> ::dafny_runtime::DafnyInt {
      ::dafny_runtime::int!(b"9223372036854775808")
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
      posInt64(1)
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
  pub struct seq16<T: ::dafny_runtime::DafnyTypeEq>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::default::Default for seq16<T> {
    fn default() -> Self {
      seq16(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::dafny_runtime::DafnyPrint for seq16<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::ops::Deref for seq16<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct seq32<T: ::dafny_runtime::DafnyTypeEq>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::default::Default for seq32<T> {
    fn default() -> Self {
      seq32(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::dafny_runtime::DafnyPrint for seq32<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::ops::Deref for seq32<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
  #[derive(Clone, PartialEq)]
  #[repr(transparent)]
  pub struct seq64<T: ::dafny_runtime::DafnyTypeEq>(pub ::dafny_runtime::Sequence<T>);
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::default::Default for seq64<T> {
    fn default() -> Self {
      seq64(::std::default::Default::default())
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::dafny_runtime::DafnyPrint for seq64<T> {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, in_seq: bool) -> ::std::fmt::Result {
      ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
    }
  }
  impl <T: Clone + ::dafny_runtime::DafnyPrint + ::dafny_runtime::DafnyTypeEq + 'static>::std::ops::Deref for seq64<T> {
    type Target = ::dafny_runtime::Sequence<T>;
    fn deref(&self) -> &Self::Target {
      &self.0
    }
  }
}
pub mod r#_StandardLibrary_Compile {
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn _allocated() -> *mut Self {
      ::dafny_runtime::allocate::<Self>()
    }
    pub fn Join<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(ss: &::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>, joiner: &::dafny_runtime::Sequence<_T>) -> ::dafny_runtime::Sequence<_T>
       where  {
      let mut _accumulator: ::dafny_runtime::Sequence<_T> = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>;
      let mut ss = ss.clone();
      let mut joiner = joiner.clone();
      let mut _accumulator = _accumulator.clone();
      'TAIL_CALL_START: loop {
        if ss.cardinality() == ::dafny_runtime::int!(1) {
          return _accumulator.concat(&ss.get(&::dafny_runtime::int!(0)));
        } else {
          _accumulator = _accumulator.concat(&ss.get(&::dafny_runtime::int!(0)).concat(&joiner));
          let mut _in0: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> = ss.drop(&::dafny_runtime::int!(1));
          let mut _in1: ::dafny_runtime::Sequence<_T> = joiner.clone();
          ss = _in0.clone();
          joiner = _in1.clone();
          continue 'TAIL_CALL_START;
        }
      }
    }
    pub fn Split<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, delim: &_T) -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>
       {
      let mut _accumulator: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>;
      let mut s = s.clone();
      let mut delim = delim.clone();
      let mut _accumulator = _accumulator.clone();
      'TAIL_CALL_START: loop {
        let mut i: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::_System::nat>> = super::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(&s, &delim, &::dafny_runtime::int!(0));
        if matches!((&i).as_ref(), super::r#_Wrappers_Compile::Option::Some{ .. }) {
          _accumulator = _accumulator.concat(&::dafny_runtime::seq![s.take((&i).value())]);
          let mut _in2: ::dafny_runtime::Sequence<_T> = s.drop(&((&i).value().clone() + ::dafny_runtime::int!(1)));
          let mut _in3: _T = delim.clone();
          s = _in2.clone();
          delim = _in3.clone();
          continue 'TAIL_CALL_START;
        } else {
          return _accumulator.concat(&::dafny_runtime::seq![s.clone()]);
        }
      }
    }
    pub fn SplitOnce<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, delim: &_T) -> (::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)
       where  {
      let mut i: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::_System::nat>> = super::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(s, delim, &::dafny_runtime::int!(0));
      (s.take((&i).value()), s.drop(&((&i).value().clone() + ::dafny_runtime::int!(1))),)
    }
    pub fn r#_SplitOnce_q<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, delim: &_T) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<(::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)>>
       where  {
      let mut valueOrError0: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::_System::nat>> = super::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(s, delim, &::dafny_runtime::int!(0));
      if valueOrError0.IsFailure() {
        (valueOrError0.PropagateFailure::<(::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)>()/* <i>Coercion from ::std::rc::Rc<super::r#_Wrappers_Compile::Option<_U>> to ::std::rc::Rc<super::r#_Wrappers_Compile::Option<(::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)>></i> not yet implemented */)
      } else {
        let mut i: super::_System::nat = (valueOrError0.Extract()/* <i>Coercion from T to ::dafny_runtime::DafnyInt</i> not yet implemented */);
        ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<(::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)>::Some {
            value: (s.take(&i), s.drop(&(i.clone() + ::dafny_runtime::int!(1))),)
          })
      }
    }
    pub fn FindIndexMatching<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, c: &_T, i: &super::_System::nat) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::_System::nat>>
       where  {
      super::r#_StandardLibrary_Compile::_default::FindIndex::<_T>(s, {
          let c: _T = c.clone();
          &(::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool>>({
                      let c = c.clone();
                      ::std::rc::Rc::new(move |x: &_T| -> bool {
                        x.clone() == c.clone()
                        })}))
          }, i)
    }
    pub fn FindIndex<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, f: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool + 'static>>, i: &super::_System::nat) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::_System::nat>>
       where  {
      let mut s = s.clone();
      let mut f = f.clone();
      let mut i = i.clone();
      'TAIL_CALL_START: loop {
        if i.clone() == s.cardinality() {
          return ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::_System::nat>::None {});
        } else {
          if ((f).0(&s.get(&i))) {
            return ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::_System::nat>::Some {
                  value: i.clone()
                });
          } else {
            let mut _in4: ::dafny_runtime::Sequence<_T> = s.clone();
            let mut _in5: ::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool + 'static>> = f.clone();
            let mut _in6: ::dafny_runtime::DafnyInt = i.clone() + ::dafny_runtime::int!(1);
            s = _in4.clone();
            f = _in5.clone();
            i = _in6.clone();
            continue 'TAIL_CALL_START;
          }
        }
      }
    }
    pub fn Filter<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>, f: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool + 'static>>) -> ::dafny_runtime::Sequence<_T>
       where  {
      let mut _accumulator: ::dafny_runtime::Sequence<_T> = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>;
      let mut s = s.clone();
      let mut f = f.clone();
      let mut _accumulator = _accumulator.clone();
      'TAIL_CALL_START: loop {
        if s.cardinality() == ::dafny_runtime::int!(0) {
          return _accumulator.concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>));
        } else {
          if ((f).0(&s.get(&::dafny_runtime::int!(0)))) {
            _accumulator = _accumulator.concat(&::dafny_runtime::seq![s.get(&::dafny_runtime::int!(0))]);
            let mut _in7: ::dafny_runtime::Sequence<_T> = s.drop(&::dafny_runtime::int!(1));
            let mut _in8: ::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool + 'static>> = f.clone();
            s = _in7.clone();
            f = _in8.clone();
            continue 'TAIL_CALL_START;
          } else {
            let mut _in9: ::dafny_runtime::Sequence<_T> = s.drop(&::dafny_runtime::int!(1));
            let mut _in10: ::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T) -> bool + 'static>> = f.clone();
            s = _in9.clone();
            f = _in10.clone();
            continue 'TAIL_CALL_START;
          }
        }
      }
    }
    pub fn Min(a: &::dafny_runtime::DafnyInt, b: &::dafny_runtime::DafnyInt) -> ::dafny_runtime::DafnyInt {
      if a.clone() < b.clone() {
        a.clone()
      } else {
        b.clone()
      }
    }
    pub fn Fill<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(value: &_T, n: &super::_System::nat) -> ::dafny_runtime::Sequence<_T>
       where  {
      {
        let _initializer = {
              let value: _T = value.clone();
              ::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(&::dafny_runtime::DafnyInt) -> _T>>({
                            let value = value.clone();
                            ::std::rc::Rc::new(move |_v0: &::dafny_runtime::DafnyInt| -> _T {
                                        value.clone()
                                        })})
              };
        ::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), n.clone()).map(|i| _initializer.0(&i)).collect::<::dafny_runtime::Sequence<_>>()
        }
    }
    pub fn SeqToArray<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Sequence<_T>) -> *mut [_T]
       where  {
      let mut _init0: ::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&::dafny_runtime::DafnyInt) -> _T + 'static>> = {
          let s: ::dafny_runtime::Sequence<_T> = s.clone();
          ::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(&::dafny_runtime::DafnyInt) -> _T>>({
                    let s = s.clone();
                    ::std::rc::Rc::new(move |i: &::dafny_runtime::DafnyInt| -> _T {
                            s.get(i)
                            })})
          };
      ::dafny_runtime::array::initialize(&s.cardinality(), _init0.0)
    }
    pub fn LexicographicLessOrEqual<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(a: &::dafny_runtime::Sequence<_T>, b: &::dafny_runtime::Sequence<_T>, less: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool + 'static>>) -> bool
       where  {
      Self::LexicographicLessOrEqualAux(a, b, less, &::dafny_runtime::int!(0))
    }
    pub fn LexicographicLessOrEqualAux<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(a: &::dafny_runtime::Sequence<_T>, b: &::dafny_runtime::Sequence<_T>, less: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool + 'static>>, lengthOfCommonPrefix: &super::_System::nat) -> bool
       where  {
      lengthOfCommonPrefix.clone() <= b.cardinality() && ::dafny_runtime::Forall::forall(&::dafny_runtime::Range(::dafny_runtime::int!(0), lengthOfCommonPrefix.clone()), {
        let a = a.clone();
        let b = b.clone();
        ::std::rc::Rc::new(move |i| a.get(i) == b.get(i))}) && (lengthOfCommonPrefix.clone() == a.cardinality() || lengthOfCommonPrefix.clone() < b.cardinality() && (((less).0(&a.get(lengthOfCommonPrefix), &b.get(lengthOfCommonPrefix)))))
    }
    pub fn SetToOrderedSequence<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(s: &::dafny_runtime::Set<::dafny_runtime::Sequence<_T>>, less: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool + 'static>>) -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>
       where  {
      let mut _accumulator: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>;
      let mut s = s.clone();
      let mut less = less.clone();
      let mut _accumulator = _accumulator.clone();
      'TAIL_CALL_START: loop {
        if s.clone() == ::dafny_runtime::set!{} {
          return _accumulator.concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>));
        } else {
          return ((&(::dafny_runtime::FunctionWrapper::<::std::rc::Rc<dyn ::std::ops::Fn(&::dafny_runtime::DafnyInt) -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>>>({
                            let s = s.clone();
                            let less = less.clone();
                            ::std::rc::Rc::new(move |r#__let_dummy_0: &::dafny_runtime::DafnyInt| -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> {
                                    let mut a = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Sequence<_T>>::new();
                                      'label_goto__ASSIGN_SUCH_THAT_0: loop {
                                            for r#__assign_such_that_0 in (&s).iter() {
                                                  a = ::dafny_runtime::MaybePlacebo::from(r#__assign_such_that_0.clone());
                                                  if s.contains(&a.read()) && super::r#_StandardLibrary_Compile::_default::IsMinimum::<_T>(&a.read(), &s, &less) {
                                                        break 'label_goto__ASSIGN_SUCH_THAT_0;
                                                      }
                                                };
                                            panic!("Halt");
                                            break;
                                          };
                                      ::dafny_runtime::seq![a.read()].concat(&super::r#_StandardLibrary_Compile::_default::SetToOrderedSequence::<_T>(&s.subtract(&::dafny_runtime::set!{a.read()}), &less))
                                    })}))).0(&::dafny_runtime::int!(0)));
        }
      }
    }
    pub fn IsMinimum<_T: Clone + ::dafny_runtime::DafnyPrint + ::std::default::Default + ::dafny_runtime::DafnyTypeEq + 'static>(a: &::dafny_runtime::Sequence<_T>, s: &::dafny_runtime::Set<::dafny_runtime::Sequence<_T>>, less: &::dafny_runtime::FunctionWrapper<::std::rc::Rc<dyn ::std::ops::Fn(&_T, &_T) -> bool + 'static>>) -> bool
       where  {
      s.contains(a) && 
      ::dafny_runtime::Forall::forall(s, {
        let a = a.clone();
        let less = less.clone();
        ::std::rc::Rc::new(move |z| Self::LexicographicLessOrEqual(&a, z, &less))
      })
    }
  }
  impl ::std::default::Default for _default {
    fn default() -> Self {
      _default::new()
    }
  }
  impl ::dafny_runtime::DafnyPrint for _default {
    fn fmt_print(&self, _formatter: &mut ::std::fmt::Formatter, _in_seq: bool) -> std::fmt::Result {
      write!(_formatter, "StandardLibrary_Compile.__default")
    }
  }
  impl ::std::cmp::PartialEq for _default {
    fn eq(&self, other: &Self) -> bool {
      ::std::ptr::eq(self, other)
    }
  }
}

pub mod r#_UTF8_Compile {
  use dafny_runtime::dafny_runtime_conversions;
  use dafny_runtime::ToPrimitive;
  use dafny_runtime::BigInt;
  use crate::UTF8;
  pub struct _default {}
  impl _default {
    pub fn new() -> Self {
      _default {}
    }
    pub fn Encode(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      UTF8::UTF8::Encode(s)
    }
    pub fn Decode(b: &::dafny_runtime::Sequence<u8>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      UTF8::UTF8::Decode(b)
    }
    
    pub fn CreateEncodeSuccess(bytes: &super::r#_UTF8_Compile::ValidUTF8Bytes) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Success {value: (bytes.clone()) })
    }
    pub fn CreateEncodeFailure(error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<super::r#_UTF8_Compile::ValidUTF8Bytes, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Failure {error: (error.clone()) })
    }
    pub fn CreateDecodeSuccess(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Success {value: (s.clone()) })
    }
    pub fn CreateDecodeFailure(error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>> {
      ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Failure {error: (error.clone()) })
    }
    pub fn IsASCIIString(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> bool {
      true
    }
    pub fn EncodeAscii(s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>) -> super::r#_UTF8_Compile::ValidUTF8Bytes {
      let mut _accumulator: super::r#_UTF8_Compile::ValidUTF8Bytes = ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>;
      let mut s = s.clone();
      'TAIL_CALL_START: loop {
        if s.cardinality() == ::dafny_runtime::DafnyInt::from(0) {
          return _accumulator.concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>));
        } else {
          let mut x: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![0 as u8];
          _accumulator = _accumulator.concat(&x);
          let mut _in0: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = s.drop(&::dafny_runtime::DafnyInt::from(1));
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
          if <(super::r#_UTF8_Compile::_default)>::Uses1Byte(&r) {
            let mut _in1: ::dafny_runtime::Sequence<u8> = a.clone();
            let mut _in2: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(1);
            let mut _in3: super::_System::nat = hi.clone();
            a = _in1.clone();
            lo = _in2.clone();
            hi = _in3.clone();
            continue 'TAIL_CALL_START;
          } else {
            if ::dafny_runtime::DafnyInt::from(2) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses2Bytes(&r) {
              let mut _in4: ::dafny_runtime::Sequence<u8> = a.clone();
              let mut _in5: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(2);
              let mut _in6: super::_System::nat = hi.clone();
              a = _in4.clone();
              lo = _in5.clone();
              hi = _in6.clone();
              continue 'TAIL_CALL_START;
            } else {
              if ::dafny_runtime::DafnyInt::from(3) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses3Bytes(&r) {
                let mut _in7: ::dafny_runtime::Sequence<u8> = a.clone();
                let mut _in8: ::dafny_runtime::DafnyInt = lo.clone() + ::dafny_runtime::DafnyInt::from(3);
                let mut _in9: super::_System::nat = hi.clone();
                a = _in7.clone();
                lo = _in8.clone();
                hi = _in9.clone();
                continue 'TAIL_CALL_START;
              } else {
                if ::dafny_runtime::DafnyInt::from(4) <= r.cardinality() && <(super::r#_UTF8_Compile::_default)>::Uses4Bytes(&r) {
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
  pub type ValidUTF8Bytes = ::dafny_runtime::Sequence<u8>;
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