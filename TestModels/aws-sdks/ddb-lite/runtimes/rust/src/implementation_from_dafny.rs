#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

mod client;
mod conversions;
mod standard_library_conversions;

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
pub mod software {
    pub mod amazon {
        pub mod cryptography {
            pub mod services {
                pub mod dynamodb {
                    pub mod internaldafny {
                        pub use dafny_runtime::DafnyPrint;
                        pub use std::cmp::Eq;
                        pub use std::convert::AsRef;
                        pub use std::default::Default;
                        pub use std::fmt::Debug;
                        pub use std::hash::Hash;

                        pub struct _default {}

                        impl _default {
                            pub fn DefaultDynamoDBClientConfigType() -> ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::DynamoDBClientConfigType>{
                                ::std::rc::Rc::new(crate::software::amazon::cryptography::services::dynamodb::internaldafny::DynamoDBClientConfigType::DynamoDBClientConfigType {})
                            }
                            pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>{
                                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>::Success {
                    value: client.clone()
                  })
                            }
                            pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>{
                                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>::Failure {
                    error: error.clone()
                  })
                            }
                        }

                        #[derive(PartialEq, Clone)]
                        pub enum DynamoDBClientConfigType {
                            DynamoDBClientConfigType {},
                        }

                        impl DynamoDBClientConfigType {}

                        impl Debug for DynamoDBClientConfigType {
                            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                            }
                        }

                        impl DafnyPrint for DynamoDBClientConfigType {
                            fn fmt_print(
                                &self,
                                _formatter: &mut ::std::fmt::Formatter,
                                _in_seq: bool,
                            ) -> std::fmt::Result {
                                match self {
                                    DynamoDBClientConfigType::DynamoDBClientConfigType {} => {
                                        write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.DynamoDBClientConfigType.DynamoDBClientConfigType")?;
                                        Ok(())
                                    }
                                }
                            }
                        }

                        impl Eq for DynamoDBClientConfigType {}

                        impl Hash for DynamoDBClientConfigType {
                            fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                match self {
                                    DynamoDBClientConfigType::DynamoDBClientConfigType {} => {}
                                }
                            }
                        }

                        impl Default for DynamoDBClientConfigType {
                            fn default() -> DynamoDBClientConfigType {
                                DynamoDBClientConfigType::DynamoDBClientConfigType {}
                            }
                        }

                        impl AsRef<DynamoDBClientConfigType> for &DynamoDBClientConfigType {
                            fn as_ref(&self) -> Self {
                                self
                            }
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

                            pub struct _default {}

                            impl _default {
                                pub fn IsValid_AttributeName(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ) -> bool {
                                    ::dafny_runtime::int!(0) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(b"65535")
                                }
                                pub fn IsValid_AttributeNameList(
                                    x: &::dafny_runtime::Sequence<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                }
                                pub fn IsValid_BatchGetRequestMap(
                                    x: &::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::KeysAndAttributes>>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(100)
                                }
                                pub fn IsValid_ConsumedCapacityUnits(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(8) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(8)
                                }
                                pub fn IsValid_IndexName(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ) -> bool {
                                    ::dafny_runtime::int!(3) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(255)
                                }
                                pub fn IsValid_ItemCollectionSizeEstimateBound(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(8) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(8)
                                }
                                pub fn IsValid_KeyList(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(100)
                                }
                                pub fn IsValid_PositiveIntegerObject(x: i32) -> bool {
                                    1 <= x
                                }
                                pub fn IsValid_ScanSegment(x: i32) -> bool {
                                    0 <= x && x <= 999999
                                }
                                pub fn IsValid_ScanTotalSegments(x: i32) -> bool {
                                    1 <= x && x <= 1000000
                                }
                                pub fn IsValid_TableName(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ) -> bool {
                                    ::dafny_runtime::int!(3) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(255)
                                }
                            }

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

                            impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType>
                                DafnyPrint for DafnyCallEvent<I, O>
                            {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        DafnyCallEvent::DafnyCallEvent { input, output } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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
                            pub enum AttributeAction {
                                ADD {},
                                PUT {},
                                DELETE {},
                            }

                            impl AttributeAction {}

                            impl Debug for AttributeAction {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for AttributeAction {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        AttributeAction::ADD {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeAction.ADD")?;
                                            Ok(())
                                        }
                                        AttributeAction::PUT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeAction.PUT")?;
                                            Ok(())
                                        }
                                        AttributeAction::DELETE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeAction.DELETE")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for AttributeAction {}

                            impl Hash for AttributeAction {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        AttributeAction::ADD {} => {}
                                        AttributeAction::PUT {} => {}
                                        AttributeAction::DELETE {} => {}
                                    }
                                }
                            }

                            impl Default for AttributeAction {
                                fn default() -> AttributeAction {
                                    AttributeAction::ADD {}
                                }
                            }

                            impl AsRef<AttributeAction> for &AttributeAction {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type AttributeName =
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

                            pub type AttributeNameList = ::dafny_runtime::Sequence<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >;

                            #[derive(PartialEq, Clone)]
                            pub enum AttributeValue {
                                S {
                  S: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                },
                N {
                  N: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                },
                B {
                  B: ::dafny_runtime::Sequence<u8>
                },
                SS {
                  SS: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>
                },
                NS {
                  NS: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>
                },
                BS {
                  BS: ::dafny_runtime::Sequence<::dafny_runtime::Sequence<u8>>
                },
                M {
                  M: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>
                },
                L {
                  L: ::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>
                },
                NULL {
                  NULL: bool
                },
                BOOL {
                  BOOL: bool
                }
              }

                            impl AttributeValue {
                                pub fn S(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        AttributeValue::S { S } => S,
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn N(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => N,
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn B(&self) -> &::dafny_runtime::Sequence<u8> {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => B,
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn SS(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<
                                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                > {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => SS,
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn NS(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<
                                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                > {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => NS,
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn BS(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::Sequence<u8>>
                                {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => BS,
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn M(&self) -> &::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>{
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => M,
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn L(&self) -> &::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>{
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => L,
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn NULL(&self) -> &bool {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => NULL,
                                        AttributeValue::BOOL { BOOL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn BOOL(&self) -> &bool {
                                    match self {
                                        AttributeValue::S { S } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::N { N } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::B { B } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::SS { SS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NS { NS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BS { BS } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::M { M } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::L { L } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        AttributeValue::BOOL { BOOL } => BOOL,
                                    }
                                }
                            }

                            impl Debug for AttributeValue {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for AttributeValue {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        AttributeValue::S { S } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.S(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                S, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::N { N } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.N(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                N, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::B { B } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.B(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                B, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::SS { SS } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.SS(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SS, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::NS { NS } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.NS(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                NS, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::BS { BS } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.BS(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                BS, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::M { M } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.M(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                M, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::L { L } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.L(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                L, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.NULL(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                NULL, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValue.BOOL(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                BOOL, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for AttributeValue {}

                            impl Hash for AttributeValue {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        AttributeValue::S { S } => {
                                            ::std::hash::Hash::hash(S, _state)
                                        }
                                        AttributeValue::N { N } => {
                                            ::std::hash::Hash::hash(N, _state)
                                        }
                                        AttributeValue::B { B } => {
                                            ::std::hash::Hash::hash(B, _state)
                                        }
                                        AttributeValue::SS { SS } => {
                                            ::std::hash::Hash::hash(SS, _state)
                                        }
                                        AttributeValue::NS { NS } => {
                                            ::std::hash::Hash::hash(NS, _state)
                                        }
                                        AttributeValue::BS { BS } => {
                                            ::std::hash::Hash::hash(BS, _state)
                                        }
                                        AttributeValue::M { M } => {
                                            ::std::hash::Hash::hash(M, _state)
                                        }
                                        AttributeValue::L { L } => {
                                            ::std::hash::Hash::hash(L, _state)
                                        }
                                        AttributeValue::NULL { NULL } => {
                                            ::std::hash::Hash::hash(NULL, _state)
                                        }
                                        AttributeValue::BOOL { BOOL } => {
                                            ::std::hash::Hash::hash(BOOL, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for AttributeValue {
                                fn default() -> AttributeValue {
                                    AttributeValue::S {
                                        S: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<AttributeValue> for &AttributeValue {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum AttributeValueUpdate {
                                AttributeValueUpdate {
                  Value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>,
                  Action: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeAction>>>
                }
              }

                            impl AttributeValueUpdate {
                                pub fn Value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>{
                                    match self {
                                        AttributeValueUpdate::AttributeValueUpdate {
                                            Value,
                                            Action,
                                        } => Value,
                                    }
                                }
                                pub fn Action(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeAction>>>{
                                    match self {
                                        AttributeValueUpdate::AttributeValueUpdate {
                                            Value,
                                            Action,
                                        } => Action,
                                    }
                                }
                            }

                            impl Debug for AttributeValueUpdate {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for AttributeValueUpdate {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        AttributeValueUpdate::AttributeValueUpdate {
                                            Value,
                                            Action,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeValueUpdate.AttributeValueUpdate(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Value, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Action, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for AttributeValueUpdate {}

                            impl Hash for AttributeValueUpdate {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        AttributeValueUpdate::AttributeValueUpdate {
                                            Value,
                                            Action,
                                        } => {
                                            ::std::hash::Hash::hash(Value, _state);
                                            ::std::hash::Hash::hash(Action, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for AttributeValueUpdate {
                                fn default() -> AttributeValueUpdate {
                                    AttributeValueUpdate::AttributeValueUpdate {
                                        Value: ::std::default::Default::default(),
                                        Action: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<AttributeValueUpdate> for &AttributeValueUpdate {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum BatchGetItemInput {
                                BatchGetItemInput {
                  RequestItems: crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetRequestMap,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>
                }
              }

                            impl BatchGetItemInput {
                                pub fn RequestItems(&self) -> &crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetRequestMap{
                                    match self {
                                        BatchGetItemInput::BatchGetItemInput {
                                            RequestItems,
                                            ReturnConsumedCapacity,
                                        } => RequestItems,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        BatchGetItemInput::BatchGetItemInput {
                                            RequestItems,
                                            ReturnConsumedCapacity,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                            }

                            impl Debug for BatchGetItemInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for BatchGetItemInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        BatchGetItemInput::BatchGetItemInput {
                                            RequestItems,
                                            ReturnConsumedCapacity,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchGetItemInput.BatchGetItemInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                RequestItems,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for BatchGetItemInput {}

                            impl Hash for BatchGetItemInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        BatchGetItemInput::BatchGetItemInput {
                                            RequestItems,
                                            ReturnConsumedCapacity,
                                        } => {
                                            ::std::hash::Hash::hash(RequestItems, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for BatchGetItemInput {
                                fn default() -> BatchGetItemInput {
                                    BatchGetItemInput::BatchGetItemInput {
                                        RequestItems: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<BatchGetItemInput> for &BatchGetItemInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum BatchGetItemOutput {
                                BatchGetItemOutput {
                  Responses: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>>,
                  UnprocessedKeys: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetRequestMap>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>>
                }
              }

                            impl BatchGetItemOutput {
                                pub fn Responses(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>>{
                                    match self {
                                        BatchGetItemOutput::BatchGetItemOutput {
                                            Responses,
                                            UnprocessedKeys,
                                            ConsumedCapacity,
                                        } => Responses,
                                    }
                                }
                                pub fn UnprocessedKeys(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetRequestMap>>{
                                    match self {
                                        BatchGetItemOutput::BatchGetItemOutput {
                                            Responses,
                                            UnprocessedKeys,
                                            ConsumedCapacity,
                                        } => UnprocessedKeys,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>>{
                                    match self {
                                        BatchGetItemOutput::BatchGetItemOutput {
                                            Responses,
                                            UnprocessedKeys,
                                            ConsumedCapacity,
                                        } => ConsumedCapacity,
                                    }
                                }
                            }

                            impl Debug for BatchGetItemOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for BatchGetItemOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        BatchGetItemOutput::BatchGetItemOutput {
                                            Responses,
                                            UnprocessedKeys,
                                            ConsumedCapacity,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchGetItemOutput.BatchGetItemOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Responses, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                UnprocessedKeys,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for BatchGetItemOutput {}

                            impl Hash for BatchGetItemOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        BatchGetItemOutput::BatchGetItemOutput {
                                            Responses,
                                            UnprocessedKeys,
                                            ConsumedCapacity,
                                        } => {
                                            ::std::hash::Hash::hash(Responses, _state);
                                            ::std::hash::Hash::hash(UnprocessedKeys, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for BatchGetItemOutput {
                                fn default() -> BatchGetItemOutput {
                                    BatchGetItemOutput::BatchGetItemOutput {
                                        Responses: ::std::default::Default::default(),
                                        UnprocessedKeys: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<BatchGetItemOutput> for &BatchGetItemOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type BatchGetRequestMap = ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::KeysAndAttributes>>;

                            #[derive(PartialEq, Clone)]
                            pub enum Capacity {
                                Capacity {
                  ReadCapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>,
                  WriteCapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>,
                  CapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>
                }
              }

                            impl Capacity {
                                pub fn ReadCapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        Capacity::Capacity {
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            CapacityUnits,
                                        } => ReadCapacityUnits,
                                    }
                                }
                                pub fn WriteCapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        Capacity::Capacity {
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            CapacityUnits,
                                        } => WriteCapacityUnits,
                                    }
                                }
                                pub fn CapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        Capacity::Capacity {
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            CapacityUnits,
                                        } => CapacityUnits,
                                    }
                                }
                            }

                            impl Debug for Capacity {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for Capacity {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        Capacity::Capacity {
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            CapacityUnits,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Capacity.Capacity(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReadCapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                WriteCapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for Capacity {}

                            impl Hash for Capacity {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        Capacity::Capacity {
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            CapacityUnits,
                                        } => {
                                            ::std::hash::Hash::hash(ReadCapacityUnits, _state);
                                            ::std::hash::Hash::hash(WriteCapacityUnits, _state);
                                            ::std::hash::Hash::hash(CapacityUnits, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for Capacity {
                                fn default() -> Capacity {
                                    Capacity::Capacity {
                                        ReadCapacityUnits: ::std::default::Default::default(),
                                        WriteCapacityUnits: ::std::default::Default::default(),
                                        CapacityUnits: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<Capacity> for &Capacity {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ComparisonOperator {
                                EQ {},
                                NE {},
                                IN {},
                                LE {},
                                LT {},
                                GE {},
                                GT {},
                                BETWEEN {},
                                NOT_NULL {},
                                NULL {},
                                CONTAINS {},
                                NOT_CONTAINS {},
                                BEGINS_WITH {},
                            }

                            impl ComparisonOperator {}

                            impl Debug for ComparisonOperator {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ComparisonOperator {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ComparisonOperator::EQ {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.EQ")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::NE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.NE")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::IN {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.IN")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::LE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.LE")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::LT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.LT")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::GE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.GE")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::GT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.GT")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::BETWEEN {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.BETWEEN")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::NOT_NULL {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.NOT__NULL")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::NULL {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.NULL")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::CONTAINS {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.CONTAINS")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::NOT_CONTAINS {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.NOT__CONTAINS")?;
                                            Ok(())
                                        }
                                        ComparisonOperator::BEGINS_WITH {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ComparisonOperator.BEGINS__WITH")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ComparisonOperator {}

                            impl Hash for ComparisonOperator {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ComparisonOperator::EQ {} => {}
                                        ComparisonOperator::NE {} => {}
                                        ComparisonOperator::IN {} => {}
                                        ComparisonOperator::LE {} => {}
                                        ComparisonOperator::LT {} => {}
                                        ComparisonOperator::GE {} => {}
                                        ComparisonOperator::GT {} => {}
                                        ComparisonOperator::BETWEEN {} => {}
                                        ComparisonOperator::NOT_NULL {} => {}
                                        ComparisonOperator::NULL {} => {}
                                        ComparisonOperator::CONTAINS {} => {}
                                        ComparisonOperator::NOT_CONTAINS {} => {}
                                        ComparisonOperator::BEGINS_WITH {} => {}
                                    }
                                }
                            }

                            impl Default for ComparisonOperator {
                                fn default() -> ComparisonOperator {
                                    ComparisonOperator::EQ {}
                                }
                            }

                            impl AsRef<ComparisonOperator> for &ComparisonOperator {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum Condition {
                                Condition {
                  AttributeValueList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ComparisonOperator: ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ComparisonOperator>
                }
              }

                            impl Condition {
                                pub fn AttributeValueList(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        Condition::Condition {
                                            AttributeValueList,
                                            ComparisonOperator,
                                        } => AttributeValueList,
                                    }
                                }
                                pub fn ComparisonOperator(&self) -> &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ComparisonOperator>{
                                    match self {
                                        Condition::Condition {
                                            AttributeValueList,
                                            ComparisonOperator,
                                        } => ComparisonOperator,
                                    }
                                }
                            }

                            impl Debug for Condition {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for Condition {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        Condition::Condition {
                                            AttributeValueList,
                                            ComparisonOperator,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Condition.Condition(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributeValueList,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ComparisonOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for Condition {}

                            impl Hash for Condition {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        Condition::Condition {
                                            AttributeValueList,
                                            ComparisonOperator,
                                        } => {
                                            ::std::hash::Hash::hash(AttributeValueList, _state);
                                            ::std::hash::Hash::hash(ComparisonOperator, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for Condition {
                                fn default() -> Condition {
                                    Condition::Condition {
                                        AttributeValueList: ::std::default::Default::default(),
                                        ComparisonOperator: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<Condition> for &Condition {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ConditionalOperator {
                                AND {},
                                OR {},
                            }

                            impl ConditionalOperator {}

                            impl Debug for ConditionalOperator {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ConditionalOperator {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ConditionalOperator::AND {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ConditionalOperator.AND")?;
                                            Ok(())
                                        }
                                        ConditionalOperator::OR {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ConditionalOperator.OR")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ConditionalOperator {}

                            impl Hash for ConditionalOperator {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ConditionalOperator::AND {} => {}
                                        ConditionalOperator::OR {} => {}
                                    }
                                }
                            }

                            impl Default for ConditionalOperator {
                                fn default() -> ConditionalOperator {
                                    ConditionalOperator::AND {}
                                }
                            }

                            impl AsRef<ConditionalOperator> for &ConditionalOperator {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ConsumedCapacity {
                                ConsumedCapacity {
                  TableName: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  CapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>,
                  ReadCapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>,
                  WriteCapacityUnits: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>,
                  Table: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>,
                  LocalSecondaryIndexes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>>,
                  GlobalSecondaryIndexes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>>
                }
              }

                            impl ConsumedCapacity {
                                pub fn TableName(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => TableName,
                                    }
                                }
                                pub fn CapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => CapacityUnits,
                                    }
                                }
                                pub fn ReadCapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => ReadCapacityUnits,
                                    }
                                }
                                pub fn WriteCapacityUnits(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacityUnits>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => WriteCapacityUnits,
                                    }
                                }
                                pub fn Table(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => Table,
                                    }
                                }
                                pub fn LocalSecondaryIndexes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => LocalSecondaryIndexes,
                                    }
                                }
                                pub fn GlobalSecondaryIndexes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Capacity>>>>{
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => GlobalSecondaryIndexes,
                                    }
                                }
                            }

                            impl Debug for ConsumedCapacity {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ConsumedCapacity {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ConsumedCapacity.ConsumedCapacity(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReadCapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                WriteCapacityUnits,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Table, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                LocalSecondaryIndexes,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GlobalSecondaryIndexes,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ConsumedCapacity {}

                            impl Hash for ConsumedCapacity {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ConsumedCapacity::ConsumedCapacity {
                                            TableName,
                                            CapacityUnits,
                                            ReadCapacityUnits,
                                            WriteCapacityUnits,
                                            Table,
                                            LocalSecondaryIndexes,
                                            GlobalSecondaryIndexes,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(CapacityUnits, _state);
                                            ::std::hash::Hash::hash(ReadCapacityUnits, _state);
                                            ::std::hash::Hash::hash(WriteCapacityUnits, _state);
                                            ::std::hash::Hash::hash(Table, _state);
                                            ::std::hash::Hash::hash(LocalSecondaryIndexes, _state);
                                            ::std::hash::Hash::hash(GlobalSecondaryIndexes, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ConsumedCapacity {
                                fn default() -> ConsumedCapacity {
                                    ConsumedCapacity::ConsumedCapacity {
                                        TableName: ::std::default::Default::default(),
                                        CapacityUnits: ::std::default::Default::default(),
                                        ReadCapacityUnits: ::std::default::Default::default(),
                                        WriteCapacityUnits: ::std::default::Default::default(),
                                        Table: ::std::default::Default::default(),
                                        LocalSecondaryIndexes: ::std::default::Default::default(),
                                        GlobalSecondaryIndexes: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ConsumedCapacity> for &ConsumedCapacity {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type ConsumedCapacityUnits = ::dafny_runtime::Sequence<u8>;

                            pub struct IDynamoDBClientCallHistory {}

                            impl IDynamoDBClientCallHistory {
                                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                                    ::dafny_runtime::allocate_object::<Self>()
                                }
                            }

                            impl UpcastObject<dyn Any>
                for crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClientCallHistory {
                ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
              }

                            pub trait IDynamoDBClient:
                                ::std::any::Any
                                + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                            {
                                fn BatchGetItem(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetItemInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetItemOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                                fn GetItem(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::GetItemInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::GetItemOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                                fn PutItem(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PutItemInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PutItemOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                                fn Query(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::QueryInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::QueryOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                                fn Scan(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                                fn UpdateItem(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateItemInput>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateItemOutput>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>>>;
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ExpectedAttributeValue {
                                ExpectedAttributeValue {
                  Value: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>,
                  Exists: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  ComparisonOperator: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ComparisonOperator>>>,
                  AttributeValueList: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>
                }
              }

                            impl ExpectedAttributeValue {
                                pub fn Value(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>{
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => Value,
                                    }
                                }
                                pub fn Exists(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => Exists,
                                    }
                                }
                                pub fn ComparisonOperator(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ComparisonOperator>>>{
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => ComparisonOperator,
                                    }
                                }
                                pub fn AttributeValueList(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => AttributeValueList,
                                    }
                                }
                            }

                            impl Debug for ExpectedAttributeValue {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ExpectedAttributeValue {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ExpectedAttributeValue.ExpectedAttributeValue(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Value, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Exists, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ComparisonOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributeValueList,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ExpectedAttributeValue {}

                            impl Hash for ExpectedAttributeValue {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ExpectedAttributeValue::ExpectedAttributeValue {
                                            Value,
                                            Exists,
                                            ComparisonOperator,
                                            AttributeValueList,
                                        } => {
                                            ::std::hash::Hash::hash(Value, _state);
                                            ::std::hash::Hash::hash(Exists, _state);
                                            ::std::hash::Hash::hash(ComparisonOperator, _state);
                                            ::std::hash::Hash::hash(AttributeValueList, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ExpectedAttributeValue {
                                fn default() -> ExpectedAttributeValue {
                                    ExpectedAttributeValue::ExpectedAttributeValue {
                                        Value: ::std::default::Default::default(),
                                        Exists: ::std::default::Default::default(),
                                        ComparisonOperator: ::std::default::Default::default(),
                                        AttributeValueList: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ExpectedAttributeValue> for &ExpectedAttributeValue {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GetItemInput {
                                GetItemInput {
                  TableName: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  Key: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>,
                  AttributesToGet: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>,
                  ConsistentRead: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>,
                  ProjectionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>
                }
              }

                            impl GetItemInput {
                                pub fn TableName(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => TableName,
                                    }
                                }
                                pub fn Key(&self) -> &::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>{
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => Key,
                                    }
                                }
                                pub fn AttributesToGet(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>{
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => AttributesToGet,
                                    }
                                }
                                pub fn ConsistentRead(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ConsistentRead,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                                pub fn ProjectionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ProjectionExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                            }

                            impl Debug for GetItemInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GetItemInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.GetItemInput.GetItemInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Key, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributesToGet,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsistentRead,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ProjectionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GetItemInput {}

                            impl Hash for GetItemInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GetItemInput::GetItemInput {
                                            TableName,
                                            Key,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(Key, _state);
                                            ::std::hash::Hash::hash(AttributesToGet, _state);
                                            ::std::hash::Hash::hash(ConsistentRead, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(ProjectionExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for GetItemInput {
                                fn default() -> GetItemInput {
                                    GetItemInput::GetItemInput {
                                        TableName: ::std::default::Default::default(),
                                        Key: ::std::default::Default::default(),
                                        AttributesToGet: ::std::default::Default::default(),
                                        ConsistentRead: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                        ProjectionExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                    }
                                }
                            }

                            impl AsRef<GetItemInput> for &GetItemInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GetItemOutput {
                                GetItemOutput {
                  Item: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>
                }
              }

                            impl GetItemOutput {
                                pub fn Item(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        GetItemOutput::GetItemOutput {
                                            Item,
                                            ConsumedCapacity,
                                        } => Item,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>{
                                    match self {
                                        GetItemOutput::GetItemOutput {
                                            Item,
                                            ConsumedCapacity,
                                        } => ConsumedCapacity,
                                    }
                                }
                            }

                            impl Debug for GetItemOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GetItemOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GetItemOutput::GetItemOutput {
                                            Item,
                                            ConsumedCapacity,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.GetItemOutput.GetItemOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Item, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GetItemOutput {}

                            impl Hash for GetItemOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GetItemOutput::GetItemOutput {
                                            Item,
                                            ConsumedCapacity,
                                        } => {
                                            ::std::hash::Hash::hash(Item, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for GetItemOutput {
                                fn default() -> GetItemOutput {
                                    GetItemOutput::GetItemOutput {
                                        Item: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<GetItemOutput> for &GetItemOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type IndexName =
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

                            #[derive(PartialEq, Clone)]
                            pub enum ItemCollectionMetrics {
                                ItemCollectionMetrics {
                  ItemCollectionKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  SizeEstimateRangeGB: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionSizeEstimateBound>>>
                }
              }

                            impl ItemCollectionMetrics {
                                pub fn ItemCollectionKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        ItemCollectionMetrics::ItemCollectionMetrics {
                                            ItemCollectionKey,
                                            SizeEstimateRangeGB,
                                        } => ItemCollectionKey,
                                    }
                                }
                                pub fn SizeEstimateRangeGB(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionSizeEstimateBound>>>{
                                    match self {
                                        ItemCollectionMetrics::ItemCollectionMetrics {
                                            ItemCollectionKey,
                                            SizeEstimateRangeGB,
                                        } => SizeEstimateRangeGB,
                                    }
                                }
                            }

                            impl Debug for ItemCollectionMetrics {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ItemCollectionMetrics {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ItemCollectionMetrics::ItemCollectionMetrics {
                                            ItemCollectionKey,
                                            SizeEstimateRangeGB,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ItemCollectionMetrics.ItemCollectionMetrics(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ItemCollectionKey,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SizeEstimateRangeGB,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ItemCollectionMetrics {}

                            impl Hash for ItemCollectionMetrics {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ItemCollectionMetrics::ItemCollectionMetrics {
                                            ItemCollectionKey,
                                            SizeEstimateRangeGB,
                                        } => {
                                            ::std::hash::Hash::hash(ItemCollectionKey, _state);
                                            ::std::hash::Hash::hash(SizeEstimateRangeGB, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ItemCollectionMetrics {
                                fn default() -> ItemCollectionMetrics {
                                    ItemCollectionMetrics::ItemCollectionMetrics {
                                        ItemCollectionKey: ::std::default::Default::default(),
                                        SizeEstimateRangeGB: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ItemCollectionMetrics> for &ItemCollectionMetrics {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type ItemCollectionSizeEstimateBound =
                                ::dafny_runtime::Sequence<u8>;

                            pub type KeyList = ::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>;

                            #[derive(PartialEq, Clone)]
                            pub enum KeysAndAttributes {
                                KeysAndAttributes {
                  Keys: crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::KeyList,
                  AttributesToGet: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>,
                  ConsistentRead: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  ProjectionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>
                }
              }

                            impl KeysAndAttributes {
                                pub fn Keys(&self) -> &crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::KeyList{
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => Keys,
                                    }
                                }
                                pub fn AttributesToGet(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>{
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => AttributesToGet,
                                    }
                                }
                                pub fn ConsistentRead(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ConsistentRead,
                                    }
                                }
                                pub fn ProjectionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ProjectionExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                            }

                            impl Debug for KeysAndAttributes {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for KeysAndAttributes {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.KeysAndAttributes.KeysAndAttributes(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Keys, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributesToGet,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsistentRead,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ProjectionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for KeysAndAttributes {}

                            impl Hash for KeysAndAttributes {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        KeysAndAttributes::KeysAndAttributes {
                                            Keys,
                                            AttributesToGet,
                                            ConsistentRead,
                                            ProjectionExpression,
                                            ExpressionAttributeNames,
                                        } => {
                                            ::std::hash::Hash::hash(Keys, _state);
                                            ::std::hash::Hash::hash(AttributesToGet, _state);
                                            ::std::hash::Hash::hash(ConsistentRead, _state);
                                            ::std::hash::Hash::hash(ProjectionExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for KeysAndAttributes {
                                fn default() -> KeysAndAttributes {
                                    KeysAndAttributes::KeysAndAttributes {
                                        Keys: ::std::default::Default::default(),
                                        AttributesToGet: ::std::default::Default::default(),
                                        ConsistentRead: ::std::default::Default::default(),
                                        ProjectionExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                    }
                                }
                            }

                            impl AsRef<KeysAndAttributes> for &KeysAndAttributes {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type PositiveIntegerObject = i32;

                            #[derive(PartialEq, Clone)]
                            pub enum PutItemInput {
                                PutItemInput {
                  TableName: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  Item: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>,
                  Expected: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ExpectedAttributeValue>>>>,
                  ReturnValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValue>>>,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>,
                  ReturnItemCollectionMetrics: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnItemCollectionMetrics>>>,
                  ConditionalOperator: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>,
                  ConditionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  ExpressionAttributeValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>
                }
              }

                            impl PutItemInput {
                                pub fn TableName(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => TableName,
                                    }
                                }
                                pub fn Item(&self) -> &::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Item,
                                    }
                                }
                                pub fn Expected(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ExpectedAttributeValue>>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Expected,
                                    }
                                }
                                pub fn ReturnValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValue>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnValues,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                                pub fn ReturnItemCollectionMetrics(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnItemCollectionMetrics>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnItemCollectionMetrics,
                                    }
                                }
                                pub fn ConditionalOperator(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConditionalOperator,
                                    }
                                }
                                pub fn ConditionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConditionExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                                pub fn ExpressionAttributeValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeValues,
                                    }
                                }
                            }

                            impl Debug for PutItemInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for PutItemInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.PutItemInput.PutItemInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Item, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Expected, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnItemCollectionMetrics,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionalOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for PutItemInput {}

                            impl Hash for PutItemInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        PutItemInput::PutItemInput {
                                            TableName,
                                            Item,
                                            Expected,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            ConditionalOperator,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(Item, _state);
                                            ::std::hash::Hash::hash(Expected, _state);
                                            ::std::hash::Hash::hash(ReturnValues, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(
                                                ReturnItemCollectionMetrics,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(ConditionalOperator, _state);
                                            ::std::hash::Hash::hash(ConditionExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeValues,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for PutItemInput {
                                fn default() -> PutItemInput {
                                    PutItemInput::PutItemInput {
                                        TableName: ::std::default::Default::default(),
                                        Item: ::std::default::Default::default(),
                                        Expected: ::std::default::Default::default(),
                                        ReturnValues: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                        ReturnItemCollectionMetrics:
                                            ::std::default::Default::default(),
                                        ConditionalOperator: ::std::default::Default::default(),
                                        ConditionExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                        ExpressionAttributeValues: ::std::default::Default::default(
                                        ),
                                    }
                                }
                            }

                            impl AsRef<PutItemInput> for &PutItemInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum PutItemOutput {
                                PutItemOutput {
                  Attributes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>,
                  ItemCollectionMetrics: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionMetrics>>>
                }
              }

                            impl PutItemOutput {
                                pub fn Attributes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        PutItemOutput::PutItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => Attributes,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>{
                                    match self {
                                        PutItemOutput::PutItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => ConsumedCapacity,
                                    }
                                }
                                pub fn ItemCollectionMetrics(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionMetrics>>>{
                                    match self {
                                        PutItemOutput::PutItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => ItemCollectionMetrics,
                                    }
                                }
                            }

                            impl Debug for PutItemOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for PutItemOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        PutItemOutput::PutItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.PutItemOutput.PutItemOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Attributes, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ItemCollectionMetrics,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for PutItemOutput {}

                            impl Hash for PutItemOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        PutItemOutput::PutItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => {
                                            ::std::hash::Hash::hash(Attributes, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(ItemCollectionMetrics, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for PutItemOutput {
                                fn default() -> PutItemOutput {
                                    PutItemOutput::PutItemOutput {
                                        Attributes: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                        ItemCollectionMetrics: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<PutItemOutput> for &PutItemOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum QueryInput {
                                QueryInput {
                  TableName: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  IndexName: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  Select: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Select>>>,
                  AttributesToGet: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>,
                  Limit: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PositiveIntegerObject>>,
                  ConsistentRead: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  KeyConditions: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>,
                  QueryFilter: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>,
                  ConditionalOperator: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>,
                  ScanIndexForward: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  ExclusiveStartKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>,
                  ProjectionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  FilterExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  KeyConditionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  ExpressionAttributeValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>
                }
              }

                            impl QueryInput {
                                pub fn TableName(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => TableName,
                                    }
                                }
                                pub fn IndexName(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => IndexName,
                                    }
                                }
                                pub fn Select(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Select>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Select,
                                    }
                                }
                                pub fn AttributesToGet(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => AttributesToGet,
                                    }
                                }
                                pub fn Limit(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PositiveIntegerObject>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Limit,
                                    }
                                }
                                pub fn ConsistentRead(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConsistentRead,
                                    }
                                }
                                pub fn KeyConditions(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => KeyConditions,
                                    }
                                }
                                pub fn QueryFilter(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => QueryFilter,
                                    }
                                }
                                pub fn ConditionalOperator(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConditionalOperator,
                                    }
                                }
                                pub fn ScanIndexForward(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ScanIndexForward,
                                    }
                                }
                                pub fn ExclusiveStartKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExclusiveStartKey,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                                pub fn ProjectionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ProjectionExpression,
                                    }
                                }
                                pub fn FilterExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => FilterExpression,
                                    }
                                }
                                pub fn KeyConditionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => KeyConditionExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                                pub fn ExpressionAttributeValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeValues,
                                    }
                                }
                            }

                            impl Debug for QueryInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for QueryInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.QueryInput.QueryInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                IndexName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Select, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributesToGet,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Limit, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsistentRead,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyConditions,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                QueryFilter,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionalOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ScanIndexForward,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExclusiveStartKey,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ProjectionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                FilterExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyConditionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for QueryInput {}

                            impl Hash for QueryInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        QueryInput::QueryInput {
                                            TableName,
                                            IndexName,
                                            Select,
                                            AttributesToGet,
                                            Limit,
                                            ConsistentRead,
                                            KeyConditions,
                                            QueryFilter,
                                            ConditionalOperator,
                                            ScanIndexForward,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            ProjectionExpression,
                                            FilterExpression,
                                            KeyConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(IndexName, _state);
                                            ::std::hash::Hash::hash(Select, _state);
                                            ::std::hash::Hash::hash(AttributesToGet, _state);
                                            ::std::hash::Hash::hash(Limit, _state);
                                            ::std::hash::Hash::hash(ConsistentRead, _state);
                                            ::std::hash::Hash::hash(KeyConditions, _state);
                                            ::std::hash::Hash::hash(QueryFilter, _state);
                                            ::std::hash::Hash::hash(ConditionalOperator, _state);
                                            ::std::hash::Hash::hash(ScanIndexForward, _state);
                                            ::std::hash::Hash::hash(ExclusiveStartKey, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(ProjectionExpression, _state);
                                            ::std::hash::Hash::hash(FilterExpression, _state);
                                            ::std::hash::Hash::hash(KeyConditionExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeValues,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for QueryInput {
                                fn default() -> QueryInput {
                                    QueryInput::QueryInput {
                                        TableName: ::std::default::Default::default(),
                                        IndexName: ::std::default::Default::default(),
                                        Select: ::std::default::Default::default(),
                                        AttributesToGet: ::std::default::Default::default(),
                                        Limit: ::std::default::Default::default(),
                                        ConsistentRead: ::std::default::Default::default(),
                                        KeyConditions: ::std::default::Default::default(),
                                        QueryFilter: ::std::default::Default::default(),
                                        ConditionalOperator: ::std::default::Default::default(),
                                        ScanIndexForward: ::std::default::Default::default(),
                                        ExclusiveStartKey: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                        ProjectionExpression: ::std::default::Default::default(),
                                        FilterExpression: ::std::default::Default::default(),
                                        KeyConditionExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                        ExpressionAttributeValues: ::std::default::Default::default(
                                        ),
                                    }
                                }
                            }

                            impl AsRef<QueryInput> for &QueryInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum QueryOutput {
                                QueryOutput {
                  Items: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>,
                  Count: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                  ScannedCount: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                  LastEvaluatedKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>
                }
              }

                            impl QueryOutput {
                                pub fn Items(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>{
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => Items,
                                    }
                                }
                                pub fn Count(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                                {
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => Count,
                                    }
                                }
                                pub fn ScannedCount(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                                {
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => ScannedCount,
                                    }
                                }
                                pub fn LastEvaluatedKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => LastEvaluatedKey,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>{
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => ConsumedCapacity,
                                    }
                                }
                            }

                            impl Debug for QueryOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for QueryOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.QueryOutput.QueryOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Items, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Count, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ScannedCount,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                LastEvaluatedKey,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for QueryOutput {}

                            impl Hash for QueryOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        QueryOutput::QueryOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => {
                                            ::std::hash::Hash::hash(Items, _state);
                                            ::std::hash::Hash::hash(Count, _state);
                                            ::std::hash::Hash::hash(ScannedCount, _state);
                                            ::std::hash::Hash::hash(LastEvaluatedKey, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for QueryOutput {
                                fn default() -> QueryOutput {
                                    QueryOutput::QueryOutput {
                                        Items: ::std::default::Default::default(),
                                        Count: ::std::default::Default::default(),
                                        ScannedCount: ::std::default::Default::default(),
                                        LastEvaluatedKey: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<QueryOutput> for &QueryOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ReturnConsumedCapacity {
                                INDEXES {},
                                TOTAL {},
                                NONE {},
                            }

                            impl ReturnConsumedCapacity {}

                            impl Debug for ReturnConsumedCapacity {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ReturnConsumedCapacity {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ReturnConsumedCapacity::INDEXES {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnConsumedCapacity.INDEXES")?;
                                            Ok(())
                                        }
                                        ReturnConsumedCapacity::TOTAL {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnConsumedCapacity.TOTAL")?;
                                            Ok(())
                                        }
                                        ReturnConsumedCapacity::NONE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnConsumedCapacity.NONE")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ReturnConsumedCapacity {}

                            impl Hash for ReturnConsumedCapacity {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ReturnConsumedCapacity::INDEXES {} => {}
                                        ReturnConsumedCapacity::TOTAL {} => {}
                                        ReturnConsumedCapacity::NONE {} => {}
                                    }
                                }
                            }

                            impl Default for ReturnConsumedCapacity {
                                fn default() -> ReturnConsumedCapacity {
                                    ReturnConsumedCapacity::INDEXES {}
                                }
                            }

                            impl AsRef<ReturnConsumedCapacity> for &ReturnConsumedCapacity {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ReturnItemCollectionMetrics {
                                SIZE {},
                                NONE {},
                            }

                            impl ReturnItemCollectionMetrics {}

                            impl Debug for ReturnItemCollectionMetrics {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ReturnItemCollectionMetrics {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ReturnItemCollectionMetrics::SIZE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnItemCollectionMetrics.SIZE")?;
                                            Ok(())
                                        }
                                        ReturnItemCollectionMetrics::NONE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnItemCollectionMetrics.NONE")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ReturnItemCollectionMetrics {}

                            impl Hash for ReturnItemCollectionMetrics {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ReturnItemCollectionMetrics::SIZE {} => {}
                                        ReturnItemCollectionMetrics::NONE {} => {}
                                    }
                                }
                            }

                            impl Default for ReturnItemCollectionMetrics {
                                fn default() -> ReturnItemCollectionMetrics {
                                    ReturnItemCollectionMetrics::SIZE {}
                                }
                            }

                            impl AsRef<ReturnItemCollectionMetrics> for &ReturnItemCollectionMetrics {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ReturnValue {
                                NONE {},
                                ALL_OLD {},
                                UPDATED_OLD {},
                                ALL_NEW {},
                                UPDATED_NEW {},
                            }

                            impl ReturnValue {}

                            impl Debug for ReturnValue {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ReturnValue {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ReturnValue::NONE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue.NONE")?;
                                            Ok(())
                                        }
                                        ReturnValue::ALL_OLD {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue.ALL__OLD")?;
                                            Ok(())
                                        }
                                        ReturnValue::UPDATED_OLD {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue.UPDATED__OLD")?;
                                            Ok(())
                                        }
                                        ReturnValue::ALL_NEW {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue.ALL__NEW")?;
                                            Ok(())
                                        }
                                        ReturnValue::UPDATED_NEW {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ReturnValue.UPDATED__NEW")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ReturnValue {}

                            impl Hash for ReturnValue {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ReturnValue::NONE {} => {}
                                        ReturnValue::ALL_OLD {} => {}
                                        ReturnValue::UPDATED_OLD {} => {}
                                        ReturnValue::ALL_NEW {} => {}
                                        ReturnValue::UPDATED_NEW {} => {}
                                    }
                                }
                            }

                            impl Default for ReturnValue {
                                fn default() -> ReturnValue {
                                    ReturnValue::NONE {}
                                }
                            }

                            impl AsRef<ReturnValue> for &ReturnValue {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ScanInput {
                                ScanInput {
                  TableName: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  IndexName: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  AttributesToGet: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>,
                  Limit: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PositiveIntegerObject>>,
                  Select: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Select>>>,
                  ScanFilter: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>,
                  ConditionalOperator: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>,
                  ExclusiveStartKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>,
                  TotalSegments: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanTotalSegments>>,
                  Segment: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanSegment>>,
                  ProjectionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  FilterExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  ExpressionAttributeValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsistentRead: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl ScanInput {
                                pub fn TableName(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => TableName,
                                    }
                                }
                                pub fn IndexName(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => IndexName,
                                    }
                                }
                                pub fn AttributesToGet(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeNameList>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => AttributesToGet,
                                    }
                                }
                                pub fn Limit(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::PositiveIntegerObject>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => Limit,
                                    }
                                }
                                pub fn Select(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Select>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => Select,
                                    }
                                }
                                pub fn ScanFilter(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Condition>>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ScanFilter,
                                    }
                                }
                                pub fn ConditionalOperator(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ConditionalOperator,
                                    }
                                }
                                pub fn ExclusiveStartKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ExclusiveStartKey,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                                pub fn TotalSegments(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanTotalSegments>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => TotalSegments,
                                    }
                                }
                                pub fn Segment(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanSegment>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => Segment,
                                    }
                                }
                                pub fn ProjectionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ProjectionExpression,
                                    }
                                }
                                pub fn FilterExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => FilterExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                                pub fn ExpressionAttributeValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ExpressionAttributeValues,
                                    }
                                }
                                pub fn ConsistentRead(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => ConsistentRead,
                                    }
                                }
                            }

                            impl Debug for ScanInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ScanInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ScanInput.ScanInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                IndexName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributesToGet,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Limit, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Select, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ScanFilter, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionalOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExclusiveStartKey,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TotalSegments,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Segment, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ProjectionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                FilterExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsistentRead,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ScanInput {}

                            impl Hash for ScanInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ScanInput::ScanInput {
                                            TableName,
                                            IndexName,
                                            AttributesToGet,
                                            Limit,
                                            Select,
                                            ScanFilter,
                                            ConditionalOperator,
                                            ExclusiveStartKey,
                                            ReturnConsumedCapacity,
                                            TotalSegments,
                                            Segment,
                                            ProjectionExpression,
                                            FilterExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                            ConsistentRead,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(IndexName, _state);
                                            ::std::hash::Hash::hash(AttributesToGet, _state);
                                            ::std::hash::Hash::hash(Limit, _state);
                                            ::std::hash::Hash::hash(Select, _state);
                                            ::std::hash::Hash::hash(ScanFilter, _state);
                                            ::std::hash::Hash::hash(ConditionalOperator, _state);
                                            ::std::hash::Hash::hash(ExclusiveStartKey, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(TotalSegments, _state);
                                            ::std::hash::Hash::hash(Segment, _state);
                                            ::std::hash::Hash::hash(ProjectionExpression, _state);
                                            ::std::hash::Hash::hash(FilterExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeValues,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(ConsistentRead, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ScanInput {
                                fn default() -> ScanInput {
                                    ScanInput::ScanInput {
                                        TableName: ::std::default::Default::default(),
                                        IndexName: ::std::default::Default::default(),
                                        AttributesToGet: ::std::default::Default::default(),
                                        Limit: ::std::default::Default::default(),
                                        Select: ::std::default::Default::default(),
                                        ScanFilter: ::std::default::Default::default(),
                                        ConditionalOperator: ::std::default::Default::default(),
                                        ExclusiveStartKey: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                        TotalSegments: ::std::default::Default::default(),
                                        Segment: ::std::default::Default::default(),
                                        ProjectionExpression: ::std::default::Default::default(),
                                        FilterExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                        ExpressionAttributeValues: ::std::default::Default::default(
                                        ),
                                        ConsistentRead: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ScanInput> for &ScanInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ScanOutput {
                                ScanOutput {
                  Items: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>,
                  Count: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                  ScannedCount: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>,
                  LastEvaluatedKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>
                }
              }

                            impl ScanOutput {
                                pub fn Items(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>>{
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => Items,
                                    }
                                }
                                pub fn Count(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                                {
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => Count,
                                    }
                                }
                                pub fn ScannedCount(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<i32>>
                                {
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => ScannedCount,
                                    }
                                }
                                pub fn LastEvaluatedKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => LastEvaluatedKey,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>{
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => ConsumedCapacity,
                                    }
                                }
                            }

                            impl Debug for ScanOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ScanOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.ScanOutput.ScanOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Items, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Count, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ScannedCount,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                LastEvaluatedKey,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ScanOutput {}

                            impl Hash for ScanOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ScanOutput::ScanOutput {
                                            Items,
                                            Count,
                                            ScannedCount,
                                            LastEvaluatedKey,
                                            ConsumedCapacity,
                                        } => {
                                            ::std::hash::Hash::hash(Items, _state);
                                            ::std::hash::Hash::hash(Count, _state);
                                            ::std::hash::Hash::hash(ScannedCount, _state);
                                            ::std::hash::Hash::hash(LastEvaluatedKey, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ScanOutput {
                                fn default() -> ScanOutput {
                                    ScanOutput::ScanOutput {
                                        Items: ::std::default::Default::default(),
                                        Count: ::std::default::Default::default(),
                                        ScannedCount: ::std::default::Default::default(),
                                        LastEvaluatedKey: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ScanOutput> for &ScanOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type ScanSegment = i32;

                            pub type ScanTotalSegments = i32;

                            #[derive(PartialEq, Clone)]
                            pub enum Select {
                                ALL_ATTRIBUTES {},
                                ALL_PROJECTED_ATTRIBUTES {},
                                SPECIFIC_ATTRIBUTES {},
                                COUNT {},
                            }

                            impl Select {}

                            impl Debug for Select {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for Select {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        Select::ALL_ATTRIBUTES {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Select.ALL__ATTRIBUTES")?;
                                            Ok(())
                                        }
                                        Select::ALL_PROJECTED_ATTRIBUTES {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Select.ALL__PROJECTED__ATTRIBUTES")?;
                                            Ok(())
                                        }
                                        Select::SPECIFIC_ATTRIBUTES {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Select.SPECIFIC__ATTRIBUTES")?;
                                            Ok(())
                                        }
                                        Select::COUNT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Select.COUNT")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for Select {}

                            impl Hash for Select {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        Select::ALL_ATTRIBUTES {} => {}
                                        Select::ALL_PROJECTED_ATTRIBUTES {} => {}
                                        Select::SPECIFIC_ATTRIBUTES {} => {}
                                        Select::COUNT {} => {}
                                    }
                                }
                            }

                            impl Default for Select {
                                fn default() -> Select {
                                    Select::ALL_ATTRIBUTES {}
                                }
                            }

                            impl AsRef<Select> for &Select {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type TableName =
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

                            #[derive(PartialEq, Clone)]
                            pub enum UpdateItemInput {
                                UpdateItemInput {
                  TableName: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  Key: ::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>,
                  AttributeUpdates: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValueUpdate>>>>,
                  Expected: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ExpectedAttributeValue>>>>,
                  ConditionalOperator: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>,
                  ReturnValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValue>>>,
                  ReturnConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>,
                  ReturnItemCollectionMetrics: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnItemCollectionMetrics>>>,
                  UpdateExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ConditionExpression: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  ExpressionAttributeNames: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  ExpressionAttributeValues: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>
                }
              }

                            impl UpdateItemInput {
                                pub fn TableName(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => TableName,
                                    }
                                }
                                pub fn Key(&self) -> &::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Key,
                                    }
                                }
                                pub fn AttributeUpdates(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValueUpdate>>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => AttributeUpdates,
                                    }
                                }
                                pub fn Expected(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ExpectedAttributeValue>>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => Expected,
                                    }
                                }
                                pub fn ConditionalOperator(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConditionalOperator,
                                    }
                                }
                                pub fn ReturnValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnValue>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnValues,
                                    }
                                }
                                pub fn ReturnConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnConsumedCapacity>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnConsumedCapacity,
                                    }
                                }
                                pub fn ReturnItemCollectionMetrics(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ReturnItemCollectionMetrics>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ReturnItemCollectionMetrics,
                                    }
                                }
                                pub fn UpdateExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => UpdateExpression,
                                    }
                                }
                                pub fn ConditionExpression(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ConditionExpression,
                                    }
                                }
                                pub fn ExpressionAttributeNames(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Map<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                > {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeNames,
                                    }
                                }
                                pub fn ExpressionAttributeValues(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => ExpressionAttributeValues,
                                    }
                                }
                            }

                            impl Debug for UpdateItemInput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for UpdateItemInput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateItemInput.UpdateItemInput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                TableName, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Key, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttributeUpdates,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Expected, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionalOperator,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ReturnItemCollectionMetrics,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                UpdateExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConditionExpression,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeNames,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ExpressionAttributeValues,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for UpdateItemInput {}

                            impl Hash for UpdateItemInput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        UpdateItemInput::UpdateItemInput {
                                            TableName,
                                            Key,
                                            AttributeUpdates,
                                            Expected,
                                            ConditionalOperator,
                                            ReturnValues,
                                            ReturnConsumedCapacity,
                                            ReturnItemCollectionMetrics,
                                            UpdateExpression,
                                            ConditionExpression,
                                            ExpressionAttributeNames,
                                            ExpressionAttributeValues,
                                        } => {
                                            ::std::hash::Hash::hash(TableName, _state);
                                            ::std::hash::Hash::hash(Key, _state);
                                            ::std::hash::Hash::hash(AttributeUpdates, _state);
                                            ::std::hash::Hash::hash(Expected, _state);
                                            ::std::hash::Hash::hash(ConditionalOperator, _state);
                                            ::std::hash::Hash::hash(ReturnValues, _state);
                                            ::std::hash::Hash::hash(ReturnConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(
                                                ReturnItemCollectionMetrics,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(UpdateExpression, _state);
                                            ::std::hash::Hash::hash(ConditionExpression, _state);
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeNames,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                ExpressionAttributeValues,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for UpdateItemInput {
                                fn default() -> UpdateItemInput {
                                    UpdateItemInput::UpdateItemInput {
                                        TableName: ::std::default::Default::default(),
                                        Key: ::std::default::Default::default(),
                                        AttributeUpdates: ::std::default::Default::default(),
                                        Expected: ::std::default::Default::default(),
                                        ConditionalOperator: ::std::default::Default::default(),
                                        ReturnValues: ::std::default::Default::default(),
                                        ReturnConsumedCapacity: ::std::default::Default::default(),
                                        ReturnItemCollectionMetrics:
                                            ::std::default::Default::default(),
                                        UpdateExpression: ::std::default::Default::default(),
                                        ConditionExpression: ::std::default::Default::default(),
                                        ExpressionAttributeNames: ::std::default::Default::default(
                                        ),
                                        ExpressionAttributeValues: ::std::default::Default::default(
                                        ),
                                    }
                                }
                            }

                            impl AsRef<UpdateItemInput> for &UpdateItemInput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum UpdateItemOutput {
                                UpdateItemOutput {
                  Attributes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>,
                  ConsumedCapacity: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>,
                  ItemCollectionMetrics: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionMetrics>>>
                }
              }

                            impl UpdateItemOutput {
                                pub fn Attributes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::AttributeValue>>>>{
                                    match self {
                                        UpdateItemOutput::UpdateItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => Attributes,
                                    }
                                }
                                pub fn ConsumedCapacity(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>>>{
                                    match self {
                                        UpdateItemOutput::UpdateItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => ConsumedCapacity,
                                    }
                                }
                                pub fn ItemCollectionMetrics(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::ItemCollectionMetrics>>>{
                                    match self {
                                        UpdateItemOutput::UpdateItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => ItemCollectionMetrics,
                                    }
                                }
                            }

                            impl Debug for UpdateItemOutput {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for UpdateItemOutput {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        UpdateItemOutput::UpdateItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.UpdateItemOutput.UpdateItemOutput(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Attributes, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ConsumedCapacity,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                ItemCollectionMetrics,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for UpdateItemOutput {}

                            impl Hash for UpdateItemOutput {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        UpdateItemOutput::UpdateItemOutput {
                                            Attributes,
                                            ConsumedCapacity,
                                            ItemCollectionMetrics,
                                        } => {
                                            ::std::hash::Hash::hash(Attributes, _state);
                                            ::std::hash::Hash::hash(ConsumedCapacity, _state);
                                            ::std::hash::Hash::hash(ItemCollectionMetrics, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for UpdateItemOutput {
                                fn default() -> UpdateItemOutput {
                                    UpdateItemOutput::UpdateItemOutput {
                                        Attributes: ::std::default::Default::default(),
                                        ConsumedCapacity: ::std::default::Default::default(),
                                        ItemCollectionMetrics: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<UpdateItemOutput> for &UpdateItemOutput {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum Error {
                                ConditionalCheckFailedException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InternalServerError {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InvalidEndpointException {
                                    Message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                ItemCollectionSizeLimitExceededException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                ProvisionedThroughputExceededException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                RequestLimitExceeded {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                ResourceNotFoundException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                TransactionConflictException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                Opaque {
                                    obj: ::dafny_runtime::Object<dyn::std::any::Any>,
                                },
                            }

                            impl Error {
                                pub fn message(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        Error::ConditionalCheckFailedException { message } => {
                                            message
                                        }
                                        Error::InternalServerError { message } => message,
                                        Error::InvalidEndpointException { Message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::ItemCollectionSizeLimitExceededException {
                                            message,
                                        } => message,
                                        Error::ProvisionedThroughputExceededException {
                                            message,
                                        } => message,
                                        Error::RequestLimitExceeded { message } => message,
                                        Error::ResourceNotFoundException { message } => message,
                                        Error::TransactionConflictException { message } => message,
                                        Error::Opaque { obj } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn Message(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        Error::ConditionalCheckFailedException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InternalServerError { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidEndpointException { Message } => Message,
                                        Error::ItemCollectionSizeLimitExceededException {
                                            message,
                                        } => panic!("field does not exist on this variant"),
                                        Error::ProvisionedThroughputExceededException {
                                            message,
                                        } => panic!("field does not exist on this variant"),
                                        Error::RequestLimitExceeded { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::ResourceNotFoundException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::TransactionConflictException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::Opaque { obj } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
                                    match self {
                                        Error::ConditionalCheckFailedException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InternalServerError { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidEndpointException { Message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::ItemCollectionSizeLimitExceededException {
                                            message,
                                        } => panic!("field does not exist on this variant"),
                                        Error::ProvisionedThroughputExceededException {
                                            message,
                                        } => panic!("field does not exist on this variant"),
                                        Error::RequestLimitExceeded { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::ResourceNotFoundException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::TransactionConflictException { message } => {
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
                                        Error::ConditionalCheckFailedException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.ConditionalCheckFailedException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InternalServerError { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.InternalServerError(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InvalidEndpointException { Message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.InvalidEndpointException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::ItemCollectionSizeLimitExceededException {
                                            message,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.ItemCollectionSizeLimitExceededException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::ProvisionedThroughputExceededException {
                                            message,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.ProvisionedThroughputExceededException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::RequestLimitExceeded { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.RequestLimitExceeded(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::ResourceNotFoundException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.ResourceNotFoundException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::TransactionConflictException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.TransactionConflictException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::Opaque { obj } => {
                                            write!(_formatter, "software.amazon.cryptography.services.dynamodb.internaldafny.types.Error.Opaque(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                obj, _formatter, false,
                                            )?;
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
                                        Error::ConditionalCheckFailedException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InternalServerError { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InvalidEndpointException { Message } => {
                                            ::std::hash::Hash::hash(Message, _state)
                                        }
                                        Error::ItemCollectionSizeLimitExceededException {
                                            message,
                                        } => ::std::hash::Hash::hash(message, _state),
                                        Error::ProvisionedThroughputExceededException {
                                            message,
                                        } => ::std::hash::Hash::hash(message, _state),
                                        Error::RequestLimitExceeded { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::ResourceNotFoundException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::TransactionConflictException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::Opaque { obj } => {
                                            ::std::hash::Hash::hash(obj, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for Error {
                                fn default() -> Error {
                                    Error::ConditionalCheckFailedException {
                                        message: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<Error> for &Error {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type OpaqueError = ::std::rc::Rc<crate::software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>;
                        }
                    }
                }
            }
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
pub mod r#_Com_Compile {
    pub mod r#_Amazonaws_Compile {}
}
pub mod _module {}
