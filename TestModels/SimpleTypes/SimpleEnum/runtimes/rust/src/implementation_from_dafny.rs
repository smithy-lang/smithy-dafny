#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod client;
pub mod types;

/// Common errors and error handling utilities.
pub mod error;

/// All operations that this crate can perform.
pub mod operation;

mod conversions;
mod standard_library_conversions;

#[cfg(feature = "wrapped-client")]
pub mod wrapped;

pub use client::Client;
pub use types::simple_enum_config::SimpleEnumConfig;

pub mod r#_Wrappers_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn Need<_E: ::dafny_runtime::DafnyType>(
            condition: bool,
            error: &_E,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Outcome<_E>> {
            if condition {
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Outcome::<_E>::Pass {})
            } else {
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Outcome::<_E>::Fail {
                    error: error.clone(),
                })
            }
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Option<T: ::dafny_runtime::DafnyType> {
        None {},
        Some { value: T },
    }

    impl<T: ::dafny_runtime::DafnyType> Option<T> {
        pub fn ToResult(
            self: &::std::rc::Rc<Self>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                T,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            let mut _source0: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<T>> = self.clone();
            if matches!(
                (&_source0).as_ref(),
                crate::r#_Wrappers_Compile::Option::None { .. }
            ) {
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                    T,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >::Failure {
                    error: ::dafny_runtime::string_utf16_of("Option is None"),
                })
            } else {
                let mut r#___mcc_h0: T = _source0.value().clone();
                let mut v: T = r#___mcc_h0.clone();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                    T,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >::Success {
                    value: v.clone(),
                })
            }
        }
        pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
            let mut _source1: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<T>> = self.clone();
            if matches!(
                (&_source1).as_ref(),
                crate::r#_Wrappers_Compile::Option::None { .. }
            ) {
                default.clone()
            } else {
                let mut r#___mcc_h0: T = _source1.value().clone();
                let mut v: T = r#___mcc_h0.clone();
                v.clone()
            }
        }
        pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
            matches!(
                self.as_ref(),
                crate::r#_Wrappers_Compile::Option::None { .. }
            )
        }
        pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType>(
            self: &::std::rc::Rc<Self>,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<_U>> {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<_U>::None {})
        }
        pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
            self.value().clone()
        }
        pub fn value(&self) -> &T {
            match self {
                Option::None {} => panic!("field does not exist on this variant"),
                Option::Some { value } => value,
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType> Debug for Option<T> {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T: ::dafny_runtime::DafnyType> DafnyPrint for Option<T> {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Option::None {} => {
                    write!(_formatter, "Wrappers_Compile.Option.None")?;
                    Ok(())
                }
                Option::Some { value } => {
                    write!(_formatter, "Wrappers_Compile.Option.Some(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType> Option<T> {
        pub fn coerce<r#__T0: ::dafny_runtime::DafnyType>(
            f_0: ::std::rc::Rc<impl ::std::ops::Fn(T) -> r#__T0 + 'static>,
        ) -> ::std::rc::Rc<impl ::std::ops::Fn(Option<T>) -> Option<r#__T0>> {
            ::std::rc::Rc::new(move |this: Self| -> Option<r#__T0> {
                match this {
                    Option::None {} => Option::None {},
                    Option::Some { value } => Option::Some {
                        value: f_0.clone()(value),
                    },
                }
            })
        }
    }

    impl<T: ::dafny_runtime::DafnyType + Eq> Eq for Option<T> {}

    impl<T: ::dafny_runtime::DafnyType + Hash> Hash for Option<T> {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Option::None {} => {}
                Option::Some { value } => ::std::hash::Hash::hash(value, _state),
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType + Default> Default for Option<T> {
        fn default() -> Option<T> {
            Option::None {}
        }
    }

    impl<T: ::dafny_runtime::DafnyType> AsRef<Option<T>> for &Option<T> {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Result<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> {
        Success { value: T },
        Failure { error: R },
    }

    impl<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> Result<T, R> {
        pub fn ToOption(
            self: &::std::rc::Rc<Self>,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<T>> {
            let mut _source2: ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<T, R>> =
                self.clone();
            if matches!(
                (&_source2).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                let mut r#___mcc_h0: T = _source2.value().clone();
                let mut s: T = r#___mcc_h0.clone();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<T>::Some {
                    value: s.clone(),
                })
            } else {
                let mut r#___mcc_h1: R = _source2.error().clone();
                let mut e: R = r#___mcc_h1.clone();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<T>::None {})
            }
        }
        pub fn UnwrapOr(self: &::std::rc::Rc<Self>, default: &T) -> T {
            let mut _source3: ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<T, R>> =
                self.clone();
            if matches!(
                (&_source3).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
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
            matches!(
                self.as_ref(),
                crate::r#_Wrappers_Compile::Result::Failure { .. }
            )
        }
        pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType>(
            self: &::std::rc::Rc<Self>,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<_U, R>> {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<_U, R>::Failure {
                error: self.error().clone(),
            })
        }
        pub fn MapFailure<_NewR: ::dafny_runtime::DafnyType>(
            self: &::std::rc::Rc<Self>,
            reWrap: &::std::rc::Rc<dyn::std::ops::Fn(&R) -> _NewR>,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<T, _NewR>> {
            let mut _source4: ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<T, R>> =
                self.clone();
            if matches!(
                (&_source4).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                let mut r#___mcc_h0: T = _source4.value().clone();
                let mut s: T = r#___mcc_h0.clone();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<T, _NewR>::Success {
                    value: s.clone(),
                })
            } else {
                let mut r#___mcc_h1: R = _source4.error().clone();
                let mut e: R = r#___mcc_h1.clone();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<T, _NewR>::Failure {
                    error: reWrap(&e),
                })
            }
        }
        pub fn Extract(self: &::std::rc::Rc<Self>) -> T {
            self.value().clone()
        }
        pub fn value(&self) -> &T {
            match self {
                Result::Success { value } => value,
                Result::Failure { error } => panic!("field does not exist on this variant"),
            }
        }
        pub fn error(&self) -> &R {
            match self {
                Result::Success { value } => panic!("field does not exist on this variant"),
                Result::Failure { error } => error,
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> Debug for Result<T, R> {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> DafnyPrint for Result<T, R> {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Result::Success { value } => {
                    write!(_formatter, "Wrappers_Compile.Result.Success(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(value, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Result::Failure { error } => {
                    write!(_formatter, "Wrappers_Compile.Result.Failure(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(error, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> Result<T, R> {
        pub fn coerce<r#__T0: ::dafny_runtime::DafnyType, r#__T1: ::dafny_runtime::DafnyType>(
            f_0: ::std::rc::Rc<impl ::std::ops::Fn(T) -> r#__T0 + 'static>,
            f_1: ::std::rc::Rc<impl ::std::ops::Fn(R) -> r#__T1 + 'static>,
        ) -> ::std::rc::Rc<impl ::std::ops::Fn(Result<T, R>) -> Result<r#__T0, r#__T1>> {
            ::std::rc::Rc::new(move |this: Self| -> Result<r#__T0, r#__T1> {
                match this {
                    Result::Success { value } => Result::Success {
                        value: f_0.clone()(value),
                    },
                    Result::Failure { error } => Result::Failure {
                        error: f_1.clone()(error),
                    },
                }
            })
        }
    }

    impl<T: ::dafny_runtime::DafnyType + Eq, R: ::dafny_runtime::DafnyType + Eq> Eq for Result<T, R> {}

    impl<T: ::dafny_runtime::DafnyType + Hash, R: ::dafny_runtime::DafnyType + Hash> Hash
        for Result<T, R>
    {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Result::Success { value } => ::std::hash::Hash::hash(value, _state),
                Result::Failure { error } => ::std::hash::Hash::hash(error, _state),
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType + Default, R: ::dafny_runtime::DafnyType + Default> Default
        for Result<T, R>
    {
        fn default() -> Result<T, R> {
            Result::Success {
                value: ::std::default::Default::default(),
            }
        }
    }

    impl<T: ::dafny_runtime::DafnyType, R: ::dafny_runtime::DafnyType> AsRef<Result<T, R>>
        for &Result<T, R>
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum Outcome<E: ::dafny_runtime::DafnyType> {
        Pass {},
        Fail { error: E },
    }

    impl<E: ::dafny_runtime::DafnyType> Outcome<E> {
        pub fn IsFailure(self: &::std::rc::Rc<Self>) -> bool {
            matches!(
                self.as_ref(),
                crate::r#_Wrappers_Compile::Outcome::Fail { .. }
            )
        }
        pub fn PropagateFailure<_U: ::dafny_runtime::DafnyType>(
            self: &::std::rc::Rc<Self>,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<_U, E>> {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<_U, E>::Failure {
                error: self.error().clone(),
            })
        }
        pub fn error(&self) -> &E {
            match self {
                Outcome::Pass {} => panic!("field does not exist on this variant"),
                Outcome::Fail { error } => error,
            }
        }
    }

    impl<E: ::dafny_runtime::DafnyType> Debug for Outcome<E> {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<E: ::dafny_runtime::DafnyType> DafnyPrint for Outcome<E> {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Outcome::Pass {} => {
                    write!(_formatter, "Wrappers_Compile.Outcome.Pass")?;
                    Ok(())
                }
                Outcome::Fail { error } => {
                    write!(_formatter, "Wrappers_Compile.Outcome.Fail(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(error, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl<E: ::dafny_runtime::DafnyType + Eq> Eq for Outcome<E> {}

    impl<E: ::dafny_runtime::DafnyType + Hash> Hash for Outcome<E> {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Outcome::Pass {} => {}
                Outcome::Fail { error } => ::std::hash::Hash::hash(error, _state),
            }
        }
    }

    impl<E: ::dafny_runtime::DafnyType + Default> Default for Outcome<E> {
        fn default() -> Outcome<E> {
            Outcome::Pass {}
        }
    }

    impl<E: ::dafny_runtime::DafnyType> AsRef<Outcome<E>> for &Outcome<E> {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod r#_StandardLibrary_Compile {
    pub struct _default {}

    impl _default {
        pub fn Join<_T: ::dafny_runtime::DafnyType>(
            ss: &::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>,
            joiner: &::dafny_runtime::Sequence<_T>,
        ) -> ::dafny_runtime::Sequence<_T> {
            let mut _accumulator: ::dafny_runtime::Sequence<_T> =
                ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>;
            let mut ss = ss.clone();
            let mut joiner = joiner.clone();
            let mut _accumulator = _accumulator.clone();
            'TAIL_CALL_START: loop {
                if ss.cardinality() == ::dafny_runtime::int!(1) {
                    return _accumulator.concat(&ss.get(&::dafny_runtime::int!(0)));
                } else {
                    _accumulator =
                        _accumulator.concat(&ss.get(&::dafny_runtime::int!(0)).concat(&joiner));
                    let mut _in0: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> =
                        ss.drop(&::dafny_runtime::int!(1));
                    let mut _in1: ::dafny_runtime::Sequence<_T> = joiner.clone();
                    ss = _in0.clone();
                    joiner = _in1.clone();
                    continue 'TAIL_CALL_START;
                }
            }
        }
        pub fn Split<_T: ::dafny_runtime::DafnyTypeEq>(
            s: &::dafny_runtime::Sequence<_T>,
            delim: &_T,
        ) -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> {
            let mut _accumulator: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> =
                ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>;
            let mut s = s.clone();
            let mut delim = delim.clone();
            let mut _accumulator = _accumulator.clone();
            'TAIL_CALL_START: loop {
                let mut i: ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Option<::dafny_runtime::_System::nat>,
                > = crate::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(
                    &s,
                    &delim,
                    &::dafny_runtime::int!(0),
                );
                if matches!(
                    (&i).as_ref(),
                    crate::r#_Wrappers_Compile::Option::Some { .. }
                ) {
                    _accumulator = _accumulator.concat(&::dafny_runtime::seq![s.take(i.value())]);
                    let mut _in2: ::dafny_runtime::Sequence<_T> =
                        s.drop(&(i.value().clone() + ::dafny_runtime::int!(1)));
                    let mut _in3: _T = delim.clone();
                    s = _in2.clone();
                    delim = _in3.clone();
                    continue 'TAIL_CALL_START;
                } else {
                    return _accumulator.concat(&::dafny_runtime::seq![s.clone()]);
                }
            }
        }
        pub fn SplitOnce<_T: ::dafny_runtime::DafnyTypeEq>(
            s: &::dafny_runtime::Sequence<_T>,
            delim: &_T,
        ) -> (::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>) {
            let mut i: ::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<::dafny_runtime::_System::nat>,
            > = crate::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(
                s,
                delim,
                &::dafny_runtime::int!(0),
            );
            (
                s.take(i.value()),
                s.drop(&(i.value().clone() + ::dafny_runtime::int!(1))),
            )
        }
        pub fn r#_SplitOnce_q<_T: ::dafny_runtime::DafnyTypeEq>(
            s: &::dafny_runtime::Sequence<_T>,
            delim: &_T,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Option<(
                ::dafny_runtime::Sequence<_T>,
                ::dafny_runtime::Sequence<_T>,
            )>,
        > {
            let mut valueOrError0: ::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<::dafny_runtime::_System::nat>,
            > = crate::r#_StandardLibrary_Compile::_default::FindIndexMatching::<_T>(
                s,
                delim,
                &::dafny_runtime::int!(0),
            );
            if valueOrError0.IsFailure() {
                valueOrError0.PropagateFailure::<(::dafny_runtime::Sequence<_T>, ::dafny_runtime::Sequence<_T>)>()
            } else {
                let mut i: ::dafny_runtime::_System::nat = valueOrError0.Extract();
                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<(
                    ::dafny_runtime::Sequence<_T>,
                    ::dafny_runtime::Sequence<_T>,
                )>::Some {
                    value: (s.take(&i), s.drop(&(i.clone() + ::dafny_runtime::int!(1)))),
                })
            }
        }
        pub fn FindIndexMatching<_T: ::dafny_runtime::DafnyTypeEq>(
            s: &::dafny_runtime::Sequence<_T>,
            c: &_T,
            i: &::dafny_runtime::_System::nat,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::_System::nat>>
        {
            crate::r#_StandardLibrary_Compile::_default::FindIndex::<_T>(
                s,
                {
                    let c: _T = c.clone();
                    &({
                        let mut c = c.clone();
                        ::std::rc::Rc::new(move |x: &_T| -> bool { x.clone() == c.clone() })
                    })
                },
                i,
            )
        }
        pub fn FindIndex<_T: ::dafny_runtime::DafnyType>(
            s: &::dafny_runtime::Sequence<_T>,
            f: &::std::rc::Rc<dyn::std::ops::Fn(&_T) -> bool>,
            i: &::dafny_runtime::_System::nat,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::_System::nat>>
        {
            let mut s = s.clone();
            let mut f = f.clone();
            let mut i = i.clone();
            'TAIL_CALL_START: loop {
                if i.clone() == s.cardinality() {
                    return ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<
                        ::dafny_runtime::_System::nat,
                    >::None {});
                } else {
                    if (&f)(&s.get(&i)) {
                        return ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<
                            ::dafny_runtime::_System::nat,
                        >::Some {
                            value: i.clone(),
                        });
                    } else {
                        let mut _in4: ::dafny_runtime::Sequence<_T> = s.clone();
                        let mut _in5: ::std::rc::Rc<dyn::std::ops::Fn(&_T) -> bool> = f.clone();
                        let mut _in6: ::dafny_runtime::DafnyInt =
                            i.clone() + ::dafny_runtime::int!(1);
                        s = _in4.clone();
                        f = _in5.clone();
                        i = _in6.clone();
                        continue 'TAIL_CALL_START;
                    }
                }
            }
        }
        pub fn Filter<_T: ::dafny_runtime::DafnyType>(
            s: &::dafny_runtime::Sequence<_T>,
            f: &::std::rc::Rc<dyn::std::ops::Fn(&_T) -> bool>,
        ) -> ::dafny_runtime::Sequence<_T> {
            let mut _accumulator: ::dafny_runtime::Sequence<_T> =
                ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>;
            let mut s = s.clone();
            let mut f = f.clone();
            let mut _accumulator = _accumulator.clone();
            'TAIL_CALL_START: loop {
                if s.cardinality() == ::dafny_runtime::int!(0) {
                    return _accumulator
                        .concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<_T>));
                } else {
                    if (&f)(&s.get(&::dafny_runtime::int!(0))) {
                        _accumulator = _accumulator
                            .concat(&::dafny_runtime::seq![s.get(&::dafny_runtime::int!(0))]);
                        let mut _in7: ::dafny_runtime::Sequence<_T> =
                            s.drop(&::dafny_runtime::int!(1));
                        let mut _in8: ::std::rc::Rc<dyn::std::ops::Fn(&_T) -> bool> = f.clone();
                        s = _in7.clone();
                        f = _in8.clone();
                        continue 'TAIL_CALL_START;
                    } else {
                        let mut _in9: ::dafny_runtime::Sequence<_T> =
                            s.drop(&::dafny_runtime::int!(1));
                        let mut _in10: ::std::rc::Rc<dyn::std::ops::Fn(&_T) -> bool> = f.clone();
                        s = _in9.clone();
                        f = _in10.clone();
                        continue 'TAIL_CALL_START;
                    }
                }
            }
        }
        pub fn Min(
            a: &::dafny_runtime::DafnyInt,
            b: &::dafny_runtime::DafnyInt,
        ) -> ::dafny_runtime::DafnyInt {
            if a.clone() < b.clone() {
                a.clone()
            } else {
                b.clone()
            }
        }
        pub fn Fill<_T: ::dafny_runtime::DafnyType>(
            value: &_T,
            n: &::dafny_runtime::_System::nat,
        ) -> ::dafny_runtime::Sequence<_T> {
            {
                let _initializer = {
                    let value: _T = value.clone();
                    {
                        let mut value = value.clone();
                        ::std::rc::Rc::new(move |_v0: &::dafny_runtime::DafnyInt| -> _T {
                            value.clone()
                        })
                    }
                };
                ::dafny_runtime::integer_range(::dafny_runtime::Zero::zero(), n.clone())
                    .map(|i| _initializer(&i))
                    .collect::<::dafny_runtime::Sequence<_>>()
            }
        }
        pub fn SeqToArray<_T: ::dafny_runtime::DafnyType>(
            s: &::dafny_runtime::Sequence<_T>,
        ) -> ::dafny_runtime::Object<[_T]> {
            let mut a = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Object<[_T]>>::new();
            let mut _init0: ::std::rc::Rc<dyn::std::ops::Fn(&::dafny_runtime::DafnyInt) -> _T> = {
                let s: ::dafny_runtime::Sequence<_T> = s.clone();
                {
                    let mut s = s.clone();
                    ::std::rc::Rc::new(move |i: &::dafny_runtime::DafnyInt| -> _T { s.get(i) })
                }
            };
            let mut _nw0: ::dafny_runtime::Object<[::std::mem::MaybeUninit<_T>]> =
                ::dafny_runtime::array::placebos_usize_object::<_T>(
                    ::dafny_runtime::DafnyUsize::into_usize(s.cardinality()),
                );
            for r#__i0_0 in
                ::dafny_runtime::integer_range(0, ::dafny_runtime::rd!(_nw0.clone()).len())
            {
                {
                    let __idx0 = ::dafny_runtime::DafnyUsize::into_usize(r#__i0_0.clone());
                    ::dafny_runtime::md!(_nw0)[__idx0] = ::std::mem::MaybeUninit::new((&_init0)(
                        &::dafny_runtime::int!(r#__i0_0.clone()),
                    ));
                }
            }
            a = ::dafny_runtime::MaybePlacebo::from(::dafny_runtime::array::construct_object(
                _nw0.clone(),
            ));
            return a.read();
        }
        pub fn LexicographicLessOrEqual<_T: ::dafny_runtime::DafnyTypeEq>(
            a: &::dafny_runtime::Sequence<_T>,
            b: &::dafny_runtime::Sequence<_T>,
            less: &::std::rc::Rc<dyn::std::ops::Fn(&_T, &_T) -> bool>,
        ) -> bool {
            ::dafny_runtime::integer_range(::dafny_runtime::int!(0), a.cardinality() + ::dafny_runtime::int!(1)).any(({
          let mut a = a.clone();
          let mut b = b.clone();
          let mut less = less.clone();
          ::std::rc::Rc::new(move |r#__exists_var_0: ::dafny_runtime::DafnyInt| -> bool{
              let mut k: ::dafny_runtime::DafnyInt = r#__exists_var_0.clone();
              ::dafny_runtime::int!(0) <= k.clone() && k.clone() <= a.cardinality() && crate::r#_StandardLibrary_Compile::_default::LexicographicLessOrEqualAux::<_T>(&a, &b, &less, &k)
            })
        }).as_ref())
        }
        pub fn LexicographicLessOrEqualAux<_T: ::dafny_runtime::DafnyTypeEq>(
            a: &::dafny_runtime::Sequence<_T>,
            b: &::dafny_runtime::Sequence<_T>,
            less: &::std::rc::Rc<dyn::std::ops::Fn(&_T, &_T) -> bool>,
            lengthOfCommonPrefix: &::dafny_runtime::_System::nat,
        ) -> bool {
            lengthOfCommonPrefix.clone() <= b.cardinality()
                && ::dafny_runtime::integer_range(
                    ::dafny_runtime::int!(0),
                    lengthOfCommonPrefix.clone(),
                )
                .all(
                    ({
                        let mut lengthOfCommonPrefix = lengthOfCommonPrefix.clone();
                        let mut a = a.clone();
                        let mut b = b.clone();
                        ::std::rc::Rc::new(
                            move |r#__forall_var_0: ::dafny_runtime::DafnyInt| -> bool {
                                let mut i: ::dafny_runtime::DafnyInt = r#__forall_var_0.clone();
                                !(::dafny_runtime::int!(0) <= i.clone()
                                    && i.clone() < lengthOfCommonPrefix.clone())
                                    || a.get(&i) == b.get(&i)
                            },
                        )
                    })
                    .as_ref(),
                )
                && (lengthOfCommonPrefix.clone() == a.cardinality()
                    || lengthOfCommonPrefix.clone() < b.cardinality()
                        && less(&a.get(lengthOfCommonPrefix), &b.get(lengthOfCommonPrefix)))
        }
        pub fn SetToOrderedSequence<_T: ::dafny_runtime::DafnyTypeEq>(
            s: &::dafny_runtime::Set<::dafny_runtime::Sequence<_T>>,
            less: &::std::rc::Rc<dyn::std::ops::Fn(&_T, &_T) -> bool>,
        ) -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> {
            let mut _accumulator: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>> =
                ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>;
            let mut s = s.clone();
            let mut less = less.clone();
            let mut _accumulator = _accumulator.clone();
            'TAIL_CALL_START: loop {
                if s.clone() == ::dafny_runtime::set! {} {
                    return _accumulator.concat(
                        &(::dafny_runtime::seq![]
                            as ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>),
                    );
                } else {
                    return (&({
                        let mut s = s.clone();
                        let mut less = less.clone();
                        ::std::rc::Rc::new(move |r#__let_dummy_0: &::dafny_runtime::DafnyInt| -> ::dafny_runtime::Sequence<::dafny_runtime::Sequence<_T>>{
                  let mut a = ::dafny_runtime::MaybePlacebo::<::dafny_runtime::Sequence<_T>>::new();
                  'label_goto__ASSIGN_SUCH_THAT_0: loop {
                    for r#__assign_such_that_0 in (&s).iter().cloned() {
                      a = ::dafny_runtime::MaybePlacebo::from(r#__assign_such_that_0.clone());
                      if s.contains(&a.read()) && crate::r#_StandardLibrary_Compile::_default::IsMinimum::<_T>(&a.read(), &s, &less) {
                        break 'label_goto__ASSIGN_SUCH_THAT_0;
                      }
                    }
                    panic!("Halt");
                    break;
                  };
                  ::dafny_runtime::seq![a.read()].concat(&crate::r#_StandardLibrary_Compile::_default::SetToOrderedSequence::<_T>(&s.subtract(&::dafny_runtime::set!{a.read()}), &less))
                })
                    }))(&::dafny_runtime::int!(0));
                }
            }
        }
        pub fn IsMinimum<_T: ::dafny_runtime::DafnyTypeEq>(
            a: &::dafny_runtime::Sequence<_T>,
            s: &::dafny_runtime::Set<::dafny_runtime::Sequence<_T>>,
            less: &::std::rc::Rc<dyn::std::ops::Fn(&_T, &_T) -> bool>,
        ) -> bool {
            s.contains(a) && s.iter().all(({
          let mut a = a.clone();
          let mut s = s.clone();
          let mut less = less.clone();
          ::std::rc::Rc::new(move |r#__forall_var_1: &::dafny_runtime::Sequence<_T>| -> bool{
              let mut z: ::dafny_runtime::Sequence<_T> = r#__forall_var_1.clone();
              !s.contains(&z) || crate::r#_StandardLibrary_Compile::_default::LexicographicLessOrEqual::<_T>(&a, &z, &less)
            })
        }).as_ref())
        }
    }

    pub mod r#_UInt_Compile {
        pub use dafny_runtime::DafnyPrint;
        pub use std::default::Default;

        pub struct _default {}

        impl _default {
            pub fn UInt8Less(a: u8, b: u8) -> bool {
                a < b
            }
            pub fn HasUint16Len<_T: ::dafny_runtime::DafnyType>(
                s: &::dafny_runtime::Sequence<_T>,
            ) -> bool {
                s.cardinality()
                    < crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::UINT16_LIMIT()
            }
            pub fn HasUint32Len<_T: ::dafny_runtime::DafnyType>(
                s: &::dafny_runtime::Sequence<_T>,
            ) -> bool {
                s.cardinality()
                    < crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::UINT32_LIMIT()
            }
            pub fn HasUint64Len<_T: ::dafny_runtime::DafnyType>(
                s: &::dafny_runtime::Sequence<_T>,
            ) -> bool {
                s.cardinality()
                    < crate::r#_StandardLibrary_Compile::r#_UInt_Compile::_default::UINT64_LIMIT()
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

        #[derive(Clone, PartialEq)]
        #[repr(transparent)]
        pub struct uint8(pub u8);

        impl uint8 {
            pub fn is(_source: u8) -> bool {
                return true;
            }
        }

        impl Default for uint8 {
            fn default() -> Self {
                uint8(::std::default::Default::default())
            }
        }

        impl DafnyPrint for uint8 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl uint16 {
            pub fn is(_source: u16) -> bool {
                return true;
            }
        }

        impl Default for uint16 {
            fn default() -> Self {
                uint16(::std::default::Default::default())
            }
        }

        impl DafnyPrint for uint16 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl uint32 {
            pub fn is(_source: u32) -> bool {
                return true;
            }
        }

        impl Default for uint32 {
            fn default() -> Self {
                uint32(::std::default::Default::default())
            }
        }

        impl DafnyPrint for uint32 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl uint64 {
            pub fn is(_source: u64) -> bool {
                return true;
            }
        }

        impl Default for uint64 {
            fn default() -> Self {
                uint64(::std::default::Default::default())
            }
        }

        impl DafnyPrint for uint64 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl int32 {
            pub fn is(_source: i32) -> bool {
                return true;
            }
        }

        impl Default for int32 {
            fn default() -> Self {
                int32(::std::default::Default::default())
            }
        }

        impl DafnyPrint for int32 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl int64 {
            pub fn is(_source: i64) -> bool {
                return true;
            }
        }

        impl Default for int64 {
            fn default() -> Self {
                int64(::std::default::Default::default())
            }
        }

        impl DafnyPrint for int64 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
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

        impl posInt64 {
            pub fn is(_source: u64) -> bool {
                let mut x: ::dafny_runtime::DafnyInt =
                    ::std::convert::Into::<::dafny_runtime::DafnyInt>::into(_source.clone());
                return ::dafny_runtime::int!(0) < x.clone()
                    && x.clone() < ::dafny_runtime::int!(b"9223372036854775808");
            }
        }

        impl Default for posInt64 {
            fn default() -> Self {
                posInt64(1)
            }
        }

        impl DafnyPrint for posInt64 {
            fn fmt_print(
                &self,
                _formatter: &mut ::std::fmt::Formatter,
                in_seq: bool,
            ) -> ::std::fmt::Result {
                ::dafny_runtime::DafnyPrint::fmt_print(&self.0, _formatter, in_seq)
            }
        }

        impl ::std::ops::Deref for posInt64 {
            type Target = u64;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        pub type seq16<T: ::dafny_runtime::DafnyType> = ::dafny_runtime::Sequence<T>;

        pub type seq32<T: ::dafny_runtime::DafnyType> = ::dafny_runtime::Sequence<T>;

        pub type seq64<T: ::dafny_runtime::DafnyType> = ::dafny_runtime::Sequence<T>;
    }
}
pub mod UTF8 {
    pub struct _default {}

    impl _default {
        pub fn CreateEncodeSuccess(
            bytes: &crate::UTF8::ValidUTF8Bytes,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                crate::UTF8::ValidUTF8Bytes,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                crate::UTF8::ValidUTF8Bytes,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Success {
                value: bytes.clone(),
            })
        }
        pub fn CreateEncodeFailure(
            error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                crate::UTF8::ValidUTF8Bytes,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                crate::UTF8::ValidUTF8Bytes,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Failure {
                error: error.clone(),
            })
        }
        pub fn CreateDecodeSuccess(
            s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Success {
                value: s.clone(),
            })
        }
        pub fn CreateDecodeFailure(
            error: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Failure {
                error: error.clone(),
            })
        }
        pub fn IsASCIIString(
            s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> bool {
            let mut _hresult: bool = <bool as std::default::Default>::default();
            let mut _hi0: ::dafny_runtime::DafnyInt = s.cardinality();
            for i in ::dafny_runtime::integer_range(::dafny_runtime::int!(0), _hi0.clone()) {
                if !(::dafny_runtime::int!(s.get(&i).0) < ::dafny_runtime::int!(128)) {
                    _hresult = false;
                    return _hresult;
                }
            }
            _hresult = true;
            return _hresult;
        }
        pub fn EncodeAscii(
            s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> crate::UTF8::ValidUTF8Bytes {
            let mut _accumulator: crate::UTF8::ValidUTF8Bytes =
                ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>;
            let mut s = s.clone();
            let mut _accumulator = _accumulator.clone();
            'TAIL_CALL_START: loop {
                if s.cardinality() == ::dafny_runtime::int!(0) {
                    return _accumulator
                        .concat(&(::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>));
                } else {
                    let mut x: ::dafny_runtime::Sequence<u8> =
                        ::dafny_runtime::seq![s.get(&::dafny_runtime::int!(0)).0 as u8];
                    _accumulator = _accumulator.concat(&x);
                    let mut _in11: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                        s.drop(&::dafny_runtime::int!(1));
                    s = _in11.clone();
                    continue 'TAIL_CALL_START;
                }
            }
        }
        pub fn Uses1Byte(s: &::dafny_runtime::Sequence<u8>) -> bool {
            0 <= s.get(&::dafny_runtime::int!(0)) && s.get(&::dafny_runtime::int!(0)) <= 127
        }
        pub fn Uses2Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
            194 <= s.get(&::dafny_runtime::int!(0))
                && s.get(&::dafny_runtime::int!(0)) <= 223
                && (128 <= s.get(&::dafny_runtime::int!(1))
                    && s.get(&::dafny_runtime::int!(1)) <= 191)
        }
        pub fn Uses3Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
            s.get(&::dafny_runtime::int!(0)) == 224
                && (160 <= s.get(&::dafny_runtime::int!(1))
                    && s.get(&::dafny_runtime::int!(1)) <= 191)
                && (128 <= s.get(&::dafny_runtime::int!(2))
                    && s.get(&::dafny_runtime::int!(2)) <= 191)
                || 225 <= s.get(&::dafny_runtime::int!(0))
                    && s.get(&::dafny_runtime::int!(0)) <= 236
                    && (128 <= s.get(&::dafny_runtime::int!(1))
                        && s.get(&::dafny_runtime::int!(1)) <= 191)
                    && (128 <= s.get(&::dafny_runtime::int!(2))
                        && s.get(&::dafny_runtime::int!(2)) <= 191)
                || s.get(&::dafny_runtime::int!(0)) == 237
                    && (128 <= s.get(&::dafny_runtime::int!(1))
                        && s.get(&::dafny_runtime::int!(1)) <= 159)
                    && (128 <= s.get(&::dafny_runtime::int!(2))
                        && s.get(&::dafny_runtime::int!(2)) <= 191)
                || 238 <= s.get(&::dafny_runtime::int!(0))
                    && s.get(&::dafny_runtime::int!(0)) <= 239
                    && (128 <= s.get(&::dafny_runtime::int!(1))
                        && s.get(&::dafny_runtime::int!(1)) <= 191)
                    && (128 <= s.get(&::dafny_runtime::int!(2))
                        && s.get(&::dafny_runtime::int!(2)) <= 191)
        }
        pub fn Uses4Bytes(s: &::dafny_runtime::Sequence<u8>) -> bool {
            s.get(&::dafny_runtime::int!(0)) == 240
                && (144 <= s.get(&::dafny_runtime::int!(1))
                    && s.get(&::dafny_runtime::int!(1)) <= 191)
                && (128 <= s.get(&::dafny_runtime::int!(2))
                    && s.get(&::dafny_runtime::int!(2)) <= 191)
                && (128 <= s.get(&::dafny_runtime::int!(3))
                    && s.get(&::dafny_runtime::int!(3)) <= 191)
                || 241 <= s.get(&::dafny_runtime::int!(0))
                    && s.get(&::dafny_runtime::int!(0)) <= 243
                    && (128 <= s.get(&::dafny_runtime::int!(1))
                        && s.get(&::dafny_runtime::int!(1)) <= 191)
                    && (128 <= s.get(&::dafny_runtime::int!(2))
                        && s.get(&::dafny_runtime::int!(2)) <= 191)
                    && (128 <= s.get(&::dafny_runtime::int!(3))
                        && s.get(&::dafny_runtime::int!(3)) <= 191)
                || s.get(&::dafny_runtime::int!(0)) == 244
                    && (128 <= s.get(&::dafny_runtime::int!(1))
                        && s.get(&::dafny_runtime::int!(1)) <= 143)
                    && (128 <= s.get(&::dafny_runtime::int!(2))
                        && s.get(&::dafny_runtime::int!(2)) <= 191)
                    && (128 <= s.get(&::dafny_runtime::int!(3))
                        && s.get(&::dafny_runtime::int!(3)) <= 191)
        }
        pub fn ValidUTF8Range(
            a: &::dafny_runtime::Sequence<u8>,
            lo: &::dafny_runtime::_System::nat,
            hi: &::dafny_runtime::_System::nat,
        ) -> bool {
            let mut a = a.clone();
            let mut lo = lo.clone();
            let mut hi = hi.clone();
            'TAIL_CALL_START: loop {
                if lo.clone() == hi.clone() {
                    return true;
                } else {
                    let mut r: ::dafny_runtime::Sequence<u8> = a.slice(&lo, &hi);
                    if crate::UTF8::_default::Uses1Byte(&r) {
                        let mut _in12: ::dafny_runtime::Sequence<u8> = a.clone();
                        let mut _in13: ::dafny_runtime::DafnyInt =
                            lo.clone() + ::dafny_runtime::int!(1);
                        let mut _in14: ::dafny_runtime::_System::nat = hi.clone();
                        a = _in12.clone();
                        lo = _in13.clone();
                        hi = _in14.clone();
                        continue 'TAIL_CALL_START;
                    } else {
                        if ::dafny_runtime::int!(2) <= r.cardinality()
                            && crate::UTF8::_default::Uses2Bytes(&r)
                        {
                            let mut _in15: ::dafny_runtime::Sequence<u8> = a.clone();
                            let mut _in16: ::dafny_runtime::DafnyInt =
                                lo.clone() + ::dafny_runtime::int!(2);
                            let mut _in17: ::dafny_runtime::_System::nat = hi.clone();
                            a = _in15.clone();
                            lo = _in16.clone();
                            hi = _in17.clone();
                            continue 'TAIL_CALL_START;
                        } else {
                            if ::dafny_runtime::int!(3) <= r.cardinality()
                                && crate::UTF8::_default::Uses3Bytes(&r)
                            {
                                let mut _in18: ::dafny_runtime::Sequence<u8> = a.clone();
                                let mut _in19: ::dafny_runtime::DafnyInt =
                                    lo.clone() + ::dafny_runtime::int!(3);
                                let mut _in20: ::dafny_runtime::_System::nat = hi.clone();
                                a = _in18.clone();
                                lo = _in19.clone();
                                hi = _in20.clone();
                                continue 'TAIL_CALL_START;
                            } else {
                                if ::dafny_runtime::int!(4) <= r.cardinality()
                                    && crate::UTF8::_default::Uses4Bytes(&r)
                                {
                                    let mut _in21: ::dafny_runtime::Sequence<u8> = a.clone();
                                    let mut _in22: ::dafny_runtime::DafnyInt =
                                        lo.clone() + ::dafny_runtime::int!(4);
                                    let mut _in23: ::dafny_runtime::_System::nat = hi.clone();
                                    a = _in21.clone();
                                    lo = _in22.clone();
                                    hi = _in23.clone();
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
            crate::UTF8::_default::ValidUTF8Range(s, &::dafny_runtime::int!(0), &s.cardinality())
        }
    }

    pub type ValidUTF8Bytes = ::dafny_runtime::Sequence<u8>;

    pub fn r#__init_ValidUTF8Bytes() -> ::dafny_runtime::Sequence<u8> {
        ::dafny_runtime::seq![] as ::dafny_runtime::Sequence<u8>
    }
}
pub mod simple {
    pub mod types {
        pub mod smithyenum {
            pub mod internaldafny {
                pub use crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient;
                pub use dafny_runtime::UpcastObject;
                pub use std::any::Any;

                pub struct _default {}

                impl _default {
                    pub fn DefaultSimpleEnumConfig() -> ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig,
                    > {
                        ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig::SimpleEnumConfig {})
                    }
                    pub fn SimpleEnum(
                        config: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumConfig>,
                    ) -> ::std::rc::Rc<
                        crate::r#_Wrappers_Compile::Result<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                            >,
                            ::std::rc::Rc<
                                crate::simple::types::smithyenum::internaldafny::types::Error,
                            >,
                        >,
                    > {
                        let mut res = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut client = ::dafny_runtime::MaybePlacebo::<
                            ::dafny_runtime::Object<
                                crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                            >,
                        >::new();
                        let mut _nw1: ::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient> = crate::simple::types::smithyenum::internaldafny::SimpleEnumClient::_allocate_object();
                        crate::simple::types::smithyenum::internaldafny::SimpleEnumClient::_ctor(
                            &_nw1,
                            &::std::rc::Rc::new(
                                crate::r#_SimpleEnumImpl_Compile::Config::Config {},
                            ),
                        );
                        client = ::dafny_runtime::MaybePlacebo::from(_nw1.clone());
                        res = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<crate::simple::types::smithyenum::internaldafny::SimpleEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Success {
                    value: client.read()
                  }));
                        return res.read();
                    }
                    pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Success {
                value: client.clone()
              })
                    }
                    pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>::Failure {
                error: error.clone()
              })
                    }
                }

                pub struct SimpleEnumClient {
                    pub r#__i_config: ::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
                }

                impl SimpleEnumClient {
                    pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                        ::dafny_runtime::allocate_object::<Self>()
                    }
                    pub fn _ctor(
                        this: &::dafny_runtime::Object<
                            crate::simple::types::smithyenum::internaldafny::SimpleEnumClient,
                        >,
                        config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
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
                    ) -> ::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>
                    {
                        self.r#__i_config.clone()
                    }
                }

                impl UpcastObject<dyn Any> for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient {
                    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
                }

                impl ISimpleTypesEnumClient for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient {
                    fn GetEnum(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out0 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnum(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out0.read());
                        return output.read();
                    }
                    fn GetEnumFirstKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out1 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumFirstKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out1.read());
                        return output.read();
                    }
                    fn GetEnumSecondKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out2 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumSecondKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out2.read());
                        return output.read();
                    }
                    fn GetEnumThirdKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>{
                        let mut output = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>>::new();
                        _out3 = ::dafny_runtime::MaybePlacebo::from(
                            crate::r#_SimpleEnumImpl_Compile::_default::GetEnumThirdKnownValueTest(
                                &self.config().clone(),
                                input,
                            ),
                        );
                        output = ::dafny_runtime::MaybePlacebo::from(_out3.read());
                        return output.read();
                    }
                }

                impl UpcastObject<dyn ISimpleTypesEnumClient>
                    for crate::simple::types::smithyenum::internaldafny::SimpleEnumClient
                {
                    ::dafny_runtime::UpcastObjectFn!(dyn crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClient);
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
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                    pub enum GetEnumInput {
                        GetEnumInput {
              value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>
            }
          }

                    impl GetEnumInput {
                        pub fn value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>{
                            match self {
                                GetEnumInput::GetEnumInput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetEnumInput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetEnumInput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetEnumInput::GetEnumInput { value } => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.GetEnumInput.GetEnumInput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetEnumInput {}

                    impl Hash for GetEnumInput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetEnumInput::GetEnumInput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetEnumInput {
                        fn default() -> GetEnumInput {
                            GetEnumInput::GetEnumInput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetEnumInput> for &GetEnumInput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum GetEnumOutput {
                        GetEnumOutput {
              value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>
            }
          }

                    impl GetEnumOutput {
                        pub fn value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape>>>{
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => value,
                            }
                        }
                    }

                    impl Debug for GetEnumOutput {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for GetEnumOutput {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.GetEnumOutput.GetEnumOutput(")?;
                                    ::dafny_runtime::DafnyPrint::fmt_print(
                                        value, _formatter, false,
                                    )?;
                                    write!(_formatter, ")")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for GetEnumOutput {}

                    impl Hash for GetEnumOutput {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                GetEnumOutput::GetEnumOutput { value } => {
                                    ::std::hash::Hash::hash(value, _state)
                                }
                            }
                        }
                    }

                    impl Default for GetEnumOutput {
                        fn default() -> GetEnumOutput {
                            GetEnumOutput::GetEnumOutput {
                                value: ::std::default::Default::default(),
                            }
                        }
                    }

                    impl AsRef<GetEnumOutput> for &GetEnumOutput {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleEnumConfig {
                        SimpleEnumConfig {},
                    }

                    impl SimpleEnumConfig {}

                    impl Debug for SimpleEnumConfig {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleEnumConfig {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleEnumConfig::SimpleEnumConfig {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumConfig.SimpleEnumConfig")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleEnumConfig {}

                    impl Hash for SimpleEnumConfig {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleEnumConfig::SimpleEnumConfig {} => {}
                            }
                        }
                    }

                    impl Default for SimpleEnumConfig {
                        fn default() -> SimpleEnumConfig {
                            SimpleEnumConfig::SimpleEnumConfig {}
                        }
                    }

                    impl AsRef<SimpleEnumConfig> for &SimpleEnumConfig {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum SimpleEnumShape {
                        FIRST {},
                        SECOND {},
                        THIRD {},
                    }

                    impl SimpleEnumShape {}

                    impl Debug for SimpleEnumShape {
                        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                        }
                    }

                    impl DafnyPrint for SimpleEnumShape {
                        fn fmt_print(
                            &self,
                            _formatter: &mut ::std::fmt::Formatter,
                            _in_seq: bool,
                        ) -> std::fmt::Result {
                            match self {
                                SimpleEnumShape::FIRST {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.FIRST")?;
                                    Ok(())
                                }
                                SimpleEnumShape::SECOND {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.SECOND")?;
                                    Ok(())
                                }
                                SimpleEnumShape::THIRD {} => {
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.SimpleEnumShape.THIRD")?;
                                    Ok(())
                                }
                            }
                        }
                    }

                    impl Eq for SimpleEnumShape {}

                    impl Hash for SimpleEnumShape {
                        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                            match self {
                                SimpleEnumShape::FIRST {} => {}
                                SimpleEnumShape::SECOND {} => {}
                                SimpleEnumShape::THIRD {} => {}
                            }
                        }
                    }

                    impl Default for SimpleEnumShape {
                        fn default() -> SimpleEnumShape {
                            SimpleEnumShape::FIRST {}
                        }
                    }

                    impl AsRef<SimpleEnumShape> for &SimpleEnumShape {
                        fn as_ref(&self) -> Self {
                            self
                        }
                    }

                    pub struct ISimpleTypesEnumClientCallHistory {}

                    impl ISimpleTypesEnumClientCallHistory {
                        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                            ::dafny_runtime::allocate_object::<Self>()
                        }
                    }

                    impl UpcastObject<dyn Any>
            for crate::simple::types::smithyenum::internaldafny::types::ISimpleTypesEnumClientCallHistory {
            ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
          }

                    pub trait ISimpleTypesEnumClient:
                        ::std::any::Any
                        + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                    {
                        fn GetEnum(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumFirstKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumSecondKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                        fn GetEnumThirdKnownValueTest(&mut self, input: &::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput>, ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>>>;
                    }

                    #[derive(PartialEq, Clone)]
                    pub enum Error {
                        CollectionOfErrors {
                            list: ::dafny_runtime::Sequence<
                                ::std::rc::Rc<
                                    crate::simple::types::smithyenum::internaldafny::types::Error,
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
                            ::std::rc::Rc<
                                crate::simple::types::smithyenum::internaldafny::types::Error,
                            >,
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
                                    write!(_formatter, "simple.types.smithyenum.internaldafny.types.Error.CollectionOfErrors(")?;
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
                                        "simple.types.smithyenum.internaldafny.types.Error.Opaque("
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

                    pub type OpaqueError = ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::Error,
                    >;
                }
            }
        }
    }
}
pub mod r#_SimpleEnumImpl_Compile {
    pub use dafny_runtime::DafnyPrint;
    pub use std::cmp::Eq;
    pub use std::convert::AsRef;
    pub use std::default::Default;
    pub use std::fmt::Debug;
    pub use std::hash::Hash;

    pub struct _default {}

    impl _default {
        pub fn GetEnum(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumFirstKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e00: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e10: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {},
            );
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
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e01: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e11: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {},
            );
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
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumSecondKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e02: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e12: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {},
            );
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
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e03: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e13: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {},
            );
            if !(_e03.clone() == _e13.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e03));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e13));
                panic!("Halt")
            };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
        }
        pub fn GetEnumThirdKnownValueTest(
            config: &::std::rc::Rc<crate::r#_SimpleEnumImpl_Compile::Config>,
            input: &::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::GetEnumInput,
            >,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
                ::std::rc::Rc<
                    crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                >,
                ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
            >,
        > {
            let mut output = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                        >,
                        ::std::rc::Rc<
                            crate::simple::types::smithyenum::internaldafny::types::Error,
                        >,
                    >,
                >,
            >::new();
            if !matches!(
                input.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e04: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = input.value().value().clone();
            let mut _e14: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {},
            );
            if !(_e04.clone() == _e14.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e04));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e14));
                panic!("Halt")
            };
            let mut res: ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput> = ::std::rc::Rc::new(crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput::GetEnumOutput {
            value: input.value().clone()
          });
            if !matches!(
                res.value().as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e05: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = res.value().value().clone();
            let mut _e15: ::std::rc::Rc<
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
            > = ::std::rc::Rc::new(
                crate::simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {},
            );
            if !(_e05.clone() == _e15.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e05));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e15));
                panic!("Halt")
            };
            output = ::dafny_runtime::MaybePlacebo::from(::std::rc::Rc::new(
                crate::r#_Wrappers_Compile::Result::<
                    ::std::rc::Rc<
                        crate::simple::types::smithyenum::internaldafny::types::GetEnumOutput,
                    >,
                    ::std::rc::Rc<crate::simple::types::smithyenum::internaldafny::types::Error>,
                >::Success {
                    value: res.clone(),
                },
            ));
            return output.read();
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
                    write!(_formatter, "SimpleEnumImpl_Compile.Config.Config")?;
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
pub mod r#_StandardLibraryInterop_Compile {
    pub use dafny_runtime::UpcastObject;
    pub use std::any::Any;

    pub struct WrappersInterop {}

    impl WrappersInterop {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn CreateStringSome(
            s: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::Some {
                value: s.clone(),
            })
        }
        pub fn CreateStringNone() -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >::None {})
        }
        pub fn CreateBooleanSome(
            b: bool,
        ) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>> {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::Some { value: b })
        }
        pub fn CreateBooleanNone() -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>> {
            ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
        }
    }

    impl UpcastObject<dyn Any> for WrappersInterop {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod _module {}
