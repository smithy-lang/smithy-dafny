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
                pub mod kms {
                    pub mod internaldafny {
                        pub use dafny_runtime::DafnyPrint;
                        pub use std::cmp::Eq;
                        pub use std::convert::AsRef;
                        pub use std::default::Default;
                        pub use std::fmt::Debug;
                        pub use std::hash::Hash;

                        pub struct _default {}

                        impl _default {
                            pub fn DefaultKMSClientConfigType() -> ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::KMSClientConfigType>{
                                ::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::KMSClientConfigType::KMSClientConfigType {})
                            }
                            pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>{
                                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>::Success {
                    value: client.clone()
                  })
                            }
                            pub fn CreateFailureOfError(error: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>{
                                ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>::Failure {
                    error: error.clone()
                  })
                            }
                        }

                        #[derive(PartialEq, Clone)]
                        pub enum KMSClientConfigType {
                            KMSClientConfigType {},
                        }

                        impl KMSClientConfigType {}

                        impl Debug for KMSClientConfigType {
                            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                            }
                        }

                        impl DafnyPrint for KMSClientConfigType {
                            fn fmt_print(
                                &self,
                                _formatter: &mut ::std::fmt::Formatter,
                                _in_seq: bool,
                            ) -> std::fmt::Result {
                                match self {
                                    KMSClientConfigType::KMSClientConfigType {} => {
                                        write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.KMSClientConfigType.KMSClientConfigType")?;
                                        Ok(())
                                    }
                                }
                            }
                        }

                        impl Eq for KMSClientConfigType {}

                        impl Hash for KMSClientConfigType {
                            fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                match self {
                                    KMSClientConfigType::KMSClientConfigType {} => {}
                                }
                            }
                        }

                        impl Default for KMSClientConfigType {
                            fn default() -> KMSClientConfigType {
                                KMSClientConfigType::KMSClientConfigType {}
                            }
                        }

                        impl AsRef<KMSClientConfigType> for &KMSClientConfigType {
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
                                pub fn IsValid_AttestationDocumentType(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(b"262144")
                                }
                                pub fn IsValid_CiphertextType(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(6144)
                                }
                                pub fn IsValid_GrantTokenList(
                                    x: &::dafny_runtime::Sequence<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                ) -> bool {
                                    ::dafny_runtime::int!(0) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(10)
                                }
                                pub fn IsValid_GrantTokenType(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(8192)
                                }
                                pub fn IsValid_KeyIdType(
                                    x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(2048)
                                }
                                pub fn IsValid_NumberOfBytesType(x: i32) -> bool {
                                    1 <= x && x <= 1024
                                }
                                pub fn IsValid_PlaintextType(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(4096)
                                }
                                pub fn IsValid_PublicKeyType(
                                    x: &::dafny_runtime::Sequence<u8>,
                                ) -> bool {
                                    ::dafny_runtime::int!(1) <= x.cardinality()
                                        && x.cardinality() <= ::dafny_runtime::int!(8192)
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
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
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

                            pub type AttestationDocumentType = ::dafny_runtime::Sequence<u8>;

                            pub type CiphertextType = ::dafny_runtime::Sequence<u8>;

                            #[derive(PartialEq, Clone)]
                            pub enum CustomerMasterKeySpec {
                                RSA_2048 {},
                                RSA_3072 {},
                                RSA_4096 {},
                                ECC_NIST_P256 {},
                                ECC_NIST_P384 {},
                                ECC_NIST_P521 {},
                                ECC_SECG_P256K1 {},
                                SYMMETRIC_DEFAULT {},
                                HMAC_224 {},
                                HMAC_256 {},
                                HMAC_384 {},
                                HMAC_512 {},
                                SM2 {},
                            }

                            impl CustomerMasterKeySpec {}

                            impl Debug for CustomerMasterKeySpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for CustomerMasterKeySpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        CustomerMasterKeySpec::RSA_2048 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__2048")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::RSA_3072 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__3072")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::RSA_4096 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__4096")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::ECC_NIST_P256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P256")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::ECC_NIST_P384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P384")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::ECC_NIST_P521 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P521")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::ECC_SECG_P256K1 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__SECG__P256K1")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::SYMMETRIC_DEFAULT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.SYMMETRIC__DEFAULT")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::HMAC_224 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__224")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::HMAC_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__256")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::HMAC_384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__384")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::HMAC_512 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__512")?;
                                            Ok(())
                                        }
                                        CustomerMasterKeySpec::SM2 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.SM2")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for CustomerMasterKeySpec {}

                            impl Hash for CustomerMasterKeySpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        CustomerMasterKeySpec::RSA_2048 {} => {}
                                        CustomerMasterKeySpec::RSA_3072 {} => {}
                                        CustomerMasterKeySpec::RSA_4096 {} => {}
                                        CustomerMasterKeySpec::ECC_NIST_P256 {} => {}
                                        CustomerMasterKeySpec::ECC_NIST_P384 {} => {}
                                        CustomerMasterKeySpec::ECC_NIST_P521 {} => {}
                                        CustomerMasterKeySpec::ECC_SECG_P256K1 {} => {}
                                        CustomerMasterKeySpec::SYMMETRIC_DEFAULT {} => {}
                                        CustomerMasterKeySpec::HMAC_224 {} => {}
                                        CustomerMasterKeySpec::HMAC_256 {} => {}
                                        CustomerMasterKeySpec::HMAC_384 {} => {}
                                        CustomerMasterKeySpec::HMAC_512 {} => {}
                                        CustomerMasterKeySpec::SM2 {} => {}
                                    }
                                }
                            }

                            impl Default for CustomerMasterKeySpec {
                                fn default() -> CustomerMasterKeySpec {
                                    CustomerMasterKeySpec::RSA_2048 {}
                                }
                            }

                            impl AsRef<CustomerMasterKeySpec> for &CustomerMasterKeySpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum DataKeySpec {
                                AES_256 {},
                                AES_128 {},
                            }

                            impl DataKeySpec {}

                            impl Debug for DataKeySpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for DataKeySpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        DataKeySpec::AES_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.AES__256")?;
                                            Ok(())
                                        }
                                        DataKeySpec::AES_128 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.AES__128")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for DataKeySpec {}

                            impl Hash for DataKeySpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        DataKeySpec::AES_256 {} => {}
                                        DataKeySpec::AES_128 {} => {}
                                    }
                                }
                            }

                            impl Default for DataKeySpec {
                                fn default() -> DataKeySpec {
                                    DataKeySpec::AES_256 {}
                                }
                            }

                            impl AsRef<DataKeySpec> for &DataKeySpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum DecryptRequest {
                                DecryptRequest {
                  CiphertextBlob: crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType,
                  EncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  Recipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl DecryptRequest {
                                pub fn CiphertextBlob(&self) -> &crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType{
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => CiphertextBlob,
                                    }
                                }
                                pub fn EncryptionContext(
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
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => EncryptionContext,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => GrantTokens,
                                    }
                                }
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => KeyId,
                                    }
                                }
                                pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => EncryptionAlgorithm,
                                    }
                                }
                                pub fn Recipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>{
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => Recipient,
                                    }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => DryRun,
                                    }
                                }
                            }

                            impl Debug for DecryptRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for DecryptRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.DecryptRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextBlob,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionContext,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Recipient, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DryRun, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for DecryptRequest {}

                            impl Hash for DecryptRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        DecryptRequest::DecryptRequest {
                                            CiphertextBlob,
                                            EncryptionContext,
                                            GrantTokens,
                                            KeyId,
                                            EncryptionAlgorithm,
                                            Recipient,
                                            DryRun,
                                        } => {
                                            ::std::hash::Hash::hash(CiphertextBlob, _state);
                                            ::std::hash::Hash::hash(EncryptionContext, _state);
                                            ::std::hash::Hash::hash(GrantTokens, _state);
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(EncryptionAlgorithm, _state);
                                            ::std::hash::Hash::hash(Recipient, _state);
                                            ::std::hash::Hash::hash(DryRun, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for DecryptRequest {
                                fn default() -> DecryptRequest {
                                    DecryptRequest::DecryptRequest {
                                        CiphertextBlob: ::std::default::Default::default(),
                                        EncryptionContext: ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                        KeyId: ::std::default::Default::default(),
                                        EncryptionAlgorithm: ::std::default::Default::default(),
                                        Recipient: ::std::default::Default::default(),
                                        DryRun: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<DecryptRequest> for &DecryptRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum DecryptResponse {
                                DecryptResponse {
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  Plaintext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>,
                  EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  CiphertextForRecipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>
                }
              }

                            impl DecryptResponse {
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => KeyId,
                                    }
                                }
                                pub fn Plaintext(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>{
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => Plaintext,
                                    }
                                }
                                pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => EncryptionAlgorithm,
                                    }
                                }
                                pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => CiphertextForRecipient,
                                    }
                                }
                            }

                            impl Debug for DecryptResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for DecryptResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse.DecryptResponse(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Plaintext, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextForRecipient,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for DecryptResponse {}

                            impl Hash for DecryptResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        DecryptResponse::DecryptResponse {
                                            KeyId,
                                            Plaintext,
                                            EncryptionAlgorithm,
                                            CiphertextForRecipient,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(Plaintext, _state);
                                            ::std::hash::Hash::hash(EncryptionAlgorithm, _state);
                                            ::std::hash::Hash::hash(CiphertextForRecipient, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for DecryptResponse {
                                fn default() -> DecryptResponse {
                                    DecryptResponse::DecryptResponse {
                                        KeyId: ::std::default::Default::default(),
                                        Plaintext: ::std::default::Default::default(),
                                        EncryptionAlgorithm: ::std::default::Default::default(),
                                        CiphertextForRecipient: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<DecryptResponse> for &DecryptResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum DeriveSharedSecretRequest {
                                DeriveSharedSecretRequest {
                  KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  KeyAgreementAlgorithm: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>,
                  PublicKey: crate::software::amazon::cryptography::services::kms::internaldafny::types::PublicKeyType,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>,
                  Recipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>
                }
              }

                            impl DeriveSharedSecretRequest {
                                pub fn KeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => KeyId,
                                    }
                                }
                                pub fn KeyAgreementAlgorithm(&self) -> &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>{
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => KeyAgreementAlgorithm,
                                    }
                                }
                                pub fn PublicKey(&self) -> &crate::software::amazon::cryptography::services::kms::internaldafny::types::PublicKeyType{
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => PublicKey,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => GrantTokens,
                                    }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => DryRun,
                                    }
                                }
                                pub fn Recipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>{
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => Recipient,
                                    }
                                }
                            }

                            impl Debug for DeriveSharedSecretRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for DeriveSharedSecretRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DeriveSharedSecretRequest.DeriveSharedSecretRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyAgreementAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                PublicKey, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DryRun, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Recipient, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for DeriveSharedSecretRequest {}

                            impl Hash for DeriveSharedSecretRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                            KeyId,
                                            KeyAgreementAlgorithm,
                                            PublicKey,
                                            GrantTokens,
                                            DryRun,
                                            Recipient,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(KeyAgreementAlgorithm, _state);
                                            ::std::hash::Hash::hash(PublicKey, _state);
                                            ::std::hash::Hash::hash(GrantTokens, _state);
                                            ::std::hash::Hash::hash(DryRun, _state);
                                            ::std::hash::Hash::hash(Recipient, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for DeriveSharedSecretRequest {
                                fn default() -> DeriveSharedSecretRequest {
                                    DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                                        KeyId: ::std::default::Default::default(),
                                        KeyAgreementAlgorithm: ::std::default::Default::default(),
                                        PublicKey: ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                        DryRun: ::std::default::Default::default(),
                                        Recipient: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<DeriveSharedSecretRequest> for &DeriveSharedSecretRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum DeriveSharedSecretResponse {
                                DeriveSharedSecretResponse {
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  SharedSecret: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>,
                  CiphertextForRecipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>,
                  KeyAgreementAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>>>,
                  KeyOrigin: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::OriginType>>>
                }
              }

                            impl DeriveSharedSecretResponse {
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => KeyId,
                  }
                                }
                                pub fn SharedSecret(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>{
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => SharedSecret,
                  }
                                }
                                pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => CiphertextForRecipient,
                  }
                                }
                                pub fn KeyAgreementAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>>>{
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => KeyAgreementAlgorithm,
                  }
                                }
                                pub fn KeyOrigin(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::OriginType>>>{
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => KeyOrigin,
                  }
                                }
                            }

                            impl Debug for DeriveSharedSecretResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for DeriveSharedSecretResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => {
                      write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DeriveSharedSecretResponse.DeriveSharedSecretResponse(")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(SharedSecret, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(CiphertextForRecipient, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeyAgreementAlgorithm, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeyOrigin, _formatter, false)?;
                      write!(_formatter, ")")?;
                      Ok(())
                    },
                  }
                                }
                            }

                            impl Eq for DeriveSharedSecretResponse {}

                            impl Hash for DeriveSharedSecretResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                    DeriveSharedSecretResponse::DeriveSharedSecretResponse{KeyId, SharedSecret, CiphertextForRecipient, KeyAgreementAlgorithm, KeyOrigin, } => {
                      ::std::hash::Hash::hash(KeyId, _state);
                      ::std::hash::Hash::hash(SharedSecret, _state);
                      ::std::hash::Hash::hash(CiphertextForRecipient, _state);
                      ::std::hash::Hash::hash(KeyAgreementAlgorithm, _state);
                      ::std::hash::Hash::hash(KeyOrigin, _state)
                    },
                  }
                                }
                            }

                            impl Default for DeriveSharedSecretResponse {
                                fn default() -> DeriveSharedSecretResponse {
                                    DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                                        KeyId: ::std::default::Default::default(),
                                        SharedSecret: ::std::default::Default::default(),
                                        CiphertextForRecipient: ::std::default::Default::default(),
                                        KeyAgreementAlgorithm: ::std::default::Default::default(),
                                        KeyOrigin: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<DeriveSharedSecretResponse> for &DeriveSharedSecretResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum EncryptionAlgorithmSpec {
                                SYMMETRIC_DEFAULT {},
                                RSAES_OAEP_SHA_1 {},
                                RSAES_OAEP_SHA_256 {},
                            }

                            impl EncryptionAlgorithmSpec {}

                            impl Debug for EncryptionAlgorithmSpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for EncryptionAlgorithmSpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.SYMMETRIC__DEFAULT")?;
                                            Ok(())
                                        }
                                        EncryptionAlgorithmSpec::RSAES_OAEP_SHA_1 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.RSAES__OAEP__SHA__1")?;
                                            Ok(())
                                        }
                                        EncryptionAlgorithmSpec::RSAES_OAEP_SHA_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.RSAES__OAEP__SHA__256")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for EncryptionAlgorithmSpec {}

                            impl Hash for EncryptionAlgorithmSpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {} => {}
                                        EncryptionAlgorithmSpec::RSAES_OAEP_SHA_1 {} => {}
                                        EncryptionAlgorithmSpec::RSAES_OAEP_SHA_256 {} => {}
                                    }
                                }
                            }

                            impl Default for EncryptionAlgorithmSpec {
                                fn default() -> EncryptionAlgorithmSpec {
                                    EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {}
                                }
                            }

                            impl AsRef<EncryptionAlgorithmSpec> for &EncryptionAlgorithmSpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum EncryptRequest {
                                EncryptRequest {
                  KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  Plaintext: crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType,
                  EncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl EncryptRequest {
                                pub fn KeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => KeyId,
                                    }
                                }
                                pub fn Plaintext(&self) -> &crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType{
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => Plaintext,
                                    }
                                }
                                pub fn EncryptionContext(
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
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => EncryptionContext,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => GrantTokens,
                                    }
                                }
                                pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => EncryptionAlgorithm,
                                    }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => DryRun,
                                    }
                                }
                            }

                            impl Debug for EncryptRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for EncryptRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest.EncryptRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Plaintext, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionContext,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DryRun, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for EncryptRequest {}

                            impl Hash for EncryptRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        EncryptRequest::EncryptRequest {
                                            KeyId,
                                            Plaintext,
                                            EncryptionContext,
                                            GrantTokens,
                                            EncryptionAlgorithm,
                                            DryRun,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(Plaintext, _state);
                                            ::std::hash::Hash::hash(EncryptionContext, _state);
                                            ::std::hash::Hash::hash(GrantTokens, _state);
                                            ::std::hash::Hash::hash(EncryptionAlgorithm, _state);
                                            ::std::hash::Hash::hash(DryRun, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for EncryptRequest {
                                fn default() -> EncryptRequest {
                                    EncryptRequest::EncryptRequest {
                                        KeyId: ::std::default::Default::default(),
                                        Plaintext: ::std::default::Default::default(),
                                        EncryptionContext: ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                        EncryptionAlgorithm: ::std::default::Default::default(),
                                        DryRun: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<EncryptRequest> for &EncryptRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum EncryptResponse {
                                EncryptResponse {
                  CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>,
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>
                }
              }

                            impl EncryptResponse {
                                pub fn CiphertextBlob(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                                        EncryptResponse::EncryptResponse {
                                            CiphertextBlob,
                                            KeyId,
                                            EncryptionAlgorithm,
                                        } => CiphertextBlob,
                                    }
                                }
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        EncryptResponse::EncryptResponse {
                                            CiphertextBlob,
                                            KeyId,
                                            EncryptionAlgorithm,
                                        } => KeyId,
                                    }
                                }
                                pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        EncryptResponse::EncryptResponse {
                                            CiphertextBlob,
                                            KeyId,
                                            EncryptionAlgorithm,
                                        } => EncryptionAlgorithm,
                                    }
                                }
                            }

                            impl Debug for EncryptResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for EncryptResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        EncryptResponse::EncryptResponse {
                                            CiphertextBlob,
                                            KeyId,
                                            EncryptionAlgorithm,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse.EncryptResponse(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextBlob,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for EncryptResponse {}

                            impl Hash for EncryptResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        EncryptResponse::EncryptResponse {
                                            CiphertextBlob,
                                            KeyId,
                                            EncryptionAlgorithm,
                                        } => {
                                            ::std::hash::Hash::hash(CiphertextBlob, _state);
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(EncryptionAlgorithm, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for EncryptResponse {
                                fn default() -> EncryptResponse {
                                    EncryptResponse::EncryptResponse {
                                        CiphertextBlob: ::std::default::Default::default(),
                                        KeyId: ::std::default::Default::default(),
                                        EncryptionAlgorithm: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<EncryptResponse> for &EncryptResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GenerateDataKeyRequest {
                                GenerateDataKeyRequest {
                  KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  EncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  NumberOfBytes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::NumberOfBytesType>>,
                  KeySpec: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DataKeySpec>>>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  Recipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl GenerateDataKeyRequest {
                                pub fn KeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => KeyId,
                                    }
                                }
                                pub fn EncryptionContext(
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
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => EncryptionContext,
                                    }
                                }
                                pub fn NumberOfBytes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::NumberOfBytesType>>{
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => NumberOfBytes,
                                    }
                                }
                                pub fn KeySpec(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DataKeySpec>>>{
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => KeySpec,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => GrantTokens,
                                    }
                                }
                                pub fn Recipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>>{
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => Recipient,
                                    }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => DryRun,
                                    }
                                }
                            }

                            impl Debug for GenerateDataKeyRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GenerateDataKeyRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest.GenerateDataKeyRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionContext,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                NumberOfBytes,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeySpec, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Recipient, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DryRun, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GenerateDataKeyRequest {}

                            impl Hash for GenerateDataKeyRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GenerateDataKeyRequest::GenerateDataKeyRequest {
                                            KeyId,
                                            EncryptionContext,
                                            NumberOfBytes,
                                            KeySpec,
                                            GrantTokens,
                                            Recipient,
                                            DryRun,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(EncryptionContext, _state);
                                            ::std::hash::Hash::hash(NumberOfBytes, _state);
                                            ::std::hash::Hash::hash(KeySpec, _state);
                                            ::std::hash::Hash::hash(GrantTokens, _state);
                                            ::std::hash::Hash::hash(Recipient, _state);
                                            ::std::hash::Hash::hash(DryRun, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for GenerateDataKeyRequest {
                                fn default() -> GenerateDataKeyRequest {
                                    GenerateDataKeyRequest::GenerateDataKeyRequest {
                                        KeyId: ::std::default::Default::default(),
                                        EncryptionContext: ::std::default::Default::default(),
                                        NumberOfBytes: ::std::default::Default::default(),
                                        KeySpec: ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                        Recipient: ::std::default::Default::default(),
                                        DryRun: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<GenerateDataKeyRequest> for &GenerateDataKeyRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GenerateDataKeyResponse {
                                GenerateDataKeyResponse {
                  CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>,
                  Plaintext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>,
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  CiphertextForRecipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>
                }
              }

                            impl GenerateDataKeyResponse {
                                pub fn CiphertextBlob(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => CiphertextBlob,
                                    }
                                }
                                pub fn Plaintext(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>>{
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => Plaintext,
                                    }
                                }
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => KeyId,
                                    }
                                }
                                pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => CiphertextForRecipient,
                                    }
                                }
                            }

                            impl Debug for GenerateDataKeyResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GenerateDataKeyResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse.GenerateDataKeyResponse(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextBlob,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                Plaintext, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextForRecipient,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GenerateDataKeyResponse {}

                            impl Hash for GenerateDataKeyResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GenerateDataKeyResponse::GenerateDataKeyResponse {
                                            CiphertextBlob,
                                            Plaintext,
                                            KeyId,
                                            CiphertextForRecipient,
                                        } => {
                                            ::std::hash::Hash::hash(CiphertextBlob, _state);
                                            ::std::hash::Hash::hash(Plaintext, _state);
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(CiphertextForRecipient, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for GenerateDataKeyResponse {
                                fn default() -> GenerateDataKeyResponse {
                                    GenerateDataKeyResponse::GenerateDataKeyResponse {
                                        CiphertextBlob: ::std::default::Default::default(),
                                        Plaintext: ::std::default::Default::default(),
                                        KeyId: ::std::default::Default::default(),
                                        CiphertextForRecipient: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<GenerateDataKeyResponse> for &GenerateDataKeyResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GenerateDataKeyWithoutPlaintextRequest {
                                GenerateDataKeyWithoutPlaintextRequest {
                  KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  EncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  KeySpec: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DataKeySpec>>>,
                  NumberOfBytes: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::NumberOfBytesType>>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl GenerateDataKeyWithoutPlaintextRequest {
                                pub fn KeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => KeyId,
                  }
                                }
                                pub fn EncryptionContext(
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
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => EncryptionContext,
                  }
                                }
                                pub fn KeySpec(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DataKeySpec>>>{
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => KeySpec,
                  }
                                }
                                pub fn NumberOfBytes(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::NumberOfBytesType>>{
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => NumberOfBytes,
                  }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => GrantTokens,
                  }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => DryRun,
                  }
                                }
                            }

                            impl Debug for GenerateDataKeyWithoutPlaintextRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GenerateDataKeyWithoutPlaintextRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => {
                      write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest.GenerateDataKeyWithoutPlaintextRequest(")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(EncryptionContext, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeySpec, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(NumberOfBytes, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                      write!(_formatter, ")")?;
                      Ok(())
                    },
                  }
                                }
                            }

                            impl Eq for GenerateDataKeyWithoutPlaintextRequest {}

                            impl Hash for GenerateDataKeyWithoutPlaintextRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => {
                      ::std::hash::Hash::hash(KeyId, _state);
                      ::std::hash::Hash::hash(EncryptionContext, _state);
                      ::std::hash::Hash::hash(KeySpec, _state);
                      ::std::hash::Hash::hash(NumberOfBytes, _state);
                      ::std::hash::Hash::hash(GrantTokens, _state);
                      ::std::hash::Hash::hash(DryRun, _state)
                    },
                  }
                                }
                            }

                            impl Default for GenerateDataKeyWithoutPlaintextRequest {
                                fn default() -> GenerateDataKeyWithoutPlaintextRequest {
                                    GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest {
                    KeyId: ::std::default::Default::default(),
                    EncryptionContext: ::std::default::Default::default(),
                    KeySpec: ::std::default::Default::default(),
                    NumberOfBytes: ::std::default::Default::default(),
                    GrantTokens: ::std::default::Default::default(),
                    DryRun: ::std::default::Default::default()
                  }
                                }
                            }

                            impl AsRef<GenerateDataKeyWithoutPlaintextRequest> for &GenerateDataKeyWithoutPlaintextRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GenerateDataKeyWithoutPlaintextResponse {
                                GenerateDataKeyWithoutPlaintextResponse {
                  CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>,
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>
                }
              }

                            impl GenerateDataKeyWithoutPlaintextResponse {
                                pub fn CiphertextBlob(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                    GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => CiphertextBlob,
                  }
                                }
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                    GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => KeyId,
                  }
                                }
                            }

                            impl Debug for GenerateDataKeyWithoutPlaintextResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GenerateDataKeyWithoutPlaintextResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                    GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => {
                      write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse.GenerateDataKeyWithoutPlaintextResponse(")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                      write!(_formatter, ", ")?;
                      ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                      write!(_formatter, ")")?;
                      Ok(())
                    },
                  }
                                }
                            }

                            impl Eq for GenerateDataKeyWithoutPlaintextResponse {}

                            impl Hash for GenerateDataKeyWithoutPlaintextResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                    GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => {
                      ::std::hash::Hash::hash(CiphertextBlob, _state);
                      ::std::hash::Hash::hash(KeyId, _state)
                    },
                  }
                                }
                            }

                            impl Default for GenerateDataKeyWithoutPlaintextResponse {
                                fn default() -> GenerateDataKeyWithoutPlaintextResponse {
                                    GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse {
                    CiphertextBlob: ::std::default::Default::default(),
                    KeyId: ::std::default::Default::default()
                  }
                                }
                            }

                            impl AsRef<GenerateDataKeyWithoutPlaintextResponse> for &GenerateDataKeyWithoutPlaintextResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GetPublicKeyRequest {
                                GetPublicKeyRequest {
                  KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>
                }
              }

                            impl GetPublicKeyRequest {
                                pub fn KeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        GetPublicKeyRequest::GetPublicKeyRequest {
                                            KeyId,
                                            GrantTokens,
                                        } => KeyId,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        GetPublicKeyRequest::GetPublicKeyRequest {
                                            KeyId,
                                            GrantTokens,
                                        } => GrantTokens,
                                    }
                                }
                            }

                            impl Debug for GetPublicKeyRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GetPublicKeyRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GetPublicKeyRequest::GetPublicKeyRequest {
                                            KeyId,
                                            GrantTokens,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest.GetPublicKeyRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GetPublicKeyRequest {}

                            impl Hash for GetPublicKeyRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GetPublicKeyRequest::GetPublicKeyRequest {
                                            KeyId,
                                            GrantTokens,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(GrantTokens, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for GetPublicKeyRequest {
                                fn default() -> GetPublicKeyRequest {
                                    GetPublicKeyRequest::GetPublicKeyRequest {
                                        KeyId: ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<GetPublicKeyRequest> for &GetPublicKeyRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum GetPublicKeyResponse {
                                GetPublicKeyResponse {
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  PublicKey: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PublicKeyType>>,
                  CustomerMasterKeySpec: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::CustomerMasterKeySpec>>>,
                  KeySpec: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeySpec>>>,
                  KeyUsage: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyUsageType>>>,
                  EncryptionAlgorithms: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>>,
                  SigningAlgorithms: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec>>>>,
                  KeyAgreementAlgorithms: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>>>>
                }
              }

                            impl GetPublicKeyResponse {
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => KeyId,
                                    }
                                }
                                pub fn PublicKey(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PublicKeyType>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => PublicKey,
                                    }
                                }
                                pub fn CustomerMasterKeySpec(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::CustomerMasterKeySpec>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => CustomerMasterKeySpec,
                                    }
                                }
                                pub fn KeySpec(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeySpec>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => KeySpec,
                                    }
                                }
                                pub fn KeyUsage(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyUsageType>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => KeyUsage,
                                    }
                                }
                                pub fn EncryptionAlgorithms(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => EncryptionAlgorithms,
                                    }
                                }
                                pub fn SigningAlgorithms(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec>>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => SigningAlgorithms,
                                    }
                                }
                                pub fn KeyAgreementAlgorithms(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyAgreementAlgorithmSpec>>>>{
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => KeyAgreementAlgorithms,
                                    }
                                }
                            }

                            impl Debug for GetPublicKeyResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for GetPublicKeyResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse.GetPublicKeyResponse(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                PublicKey, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CustomerMasterKeySpec,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeySpec, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyUsage, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                EncryptionAlgorithms,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SigningAlgorithms,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyAgreementAlgorithms,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for GetPublicKeyResponse {}

                            impl Hash for GetPublicKeyResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        GetPublicKeyResponse::GetPublicKeyResponse {
                                            KeyId,
                                            PublicKey,
                                            CustomerMasterKeySpec,
                                            KeySpec,
                                            KeyUsage,
                                            EncryptionAlgorithms,
                                            SigningAlgorithms,
                                            KeyAgreementAlgorithms,
                                        } => {
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(PublicKey, _state);
                                            ::std::hash::Hash::hash(CustomerMasterKeySpec, _state);
                                            ::std::hash::Hash::hash(KeySpec, _state);
                                            ::std::hash::Hash::hash(KeyUsage, _state);
                                            ::std::hash::Hash::hash(EncryptionAlgorithms, _state);
                                            ::std::hash::Hash::hash(SigningAlgorithms, _state);
                                            ::std::hash::Hash::hash(KeyAgreementAlgorithms, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for GetPublicKeyResponse {
                                fn default() -> GetPublicKeyResponse {
                                    GetPublicKeyResponse::GetPublicKeyResponse {
                                        KeyId: ::std::default::Default::default(),
                                        PublicKey: ::std::default::Default::default(),
                                        CustomerMasterKeySpec: ::std::default::Default::default(),
                                        KeySpec: ::std::default::Default::default(),
                                        KeyUsage: ::std::default::Default::default(),
                                        EncryptionAlgorithms: ::std::default::Default::default(),
                                        SigningAlgorithms: ::std::default::Default::default(),
                                        KeyAgreementAlgorithms: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<GetPublicKeyResponse> for &GetPublicKeyResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type GrantTokenList = ::dafny_runtime::Sequence<
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                            >;

                            pub type GrantTokenType =
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

                            #[derive(PartialEq, Clone)]
                            pub enum KeyAgreementAlgorithmSpec {
                                ECDH {},
                            }

                            impl KeyAgreementAlgorithmSpec {}

                            impl Debug for KeyAgreementAlgorithmSpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for KeyAgreementAlgorithmSpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        KeyAgreementAlgorithmSpec::ECDH {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyAgreementAlgorithmSpec.ECDH")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for KeyAgreementAlgorithmSpec {}

                            impl Hash for KeyAgreementAlgorithmSpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        KeyAgreementAlgorithmSpec::ECDH {} => {}
                                    }
                                }
                            }

                            impl Default for KeyAgreementAlgorithmSpec {
                                fn default() -> KeyAgreementAlgorithmSpec {
                                    KeyAgreementAlgorithmSpec::ECDH {}
                                }
                            }

                            impl AsRef<KeyAgreementAlgorithmSpec> for &KeyAgreementAlgorithmSpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum KeyEncryptionMechanism {
                                RSAES_OAEP_SHA_256 {},
                            }

                            impl KeyEncryptionMechanism {}

                            impl Debug for KeyEncryptionMechanism {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for KeyEncryptionMechanism {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyEncryptionMechanism.RSAES__OAEP__SHA__256")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for KeyEncryptionMechanism {}

                            impl Hash for KeyEncryptionMechanism {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {} => {}
                                    }
                                }
                            }

                            impl Default for KeyEncryptionMechanism {
                                fn default() -> KeyEncryptionMechanism {
                                    KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {}
                                }
                            }

                            impl AsRef<KeyEncryptionMechanism> for &KeyEncryptionMechanism {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type KeyIdType =
                                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

                            #[derive(PartialEq, Clone)]
                            pub enum KeySpec {
                                RSA_2048 {},
                                RSA_3072 {},
                                RSA_4096 {},
                                ECC_NIST_P256 {},
                                ECC_NIST_P384 {},
                                ECC_NIST_P521 {},
                                ECC_SECG_P256K1 {},
                                SYMMETRIC_DEFAULT {},
                                HMAC_224 {},
                                HMAC_256 {},
                                HMAC_384 {},
                                HMAC_512 {},
                                SM2 {},
                            }

                            impl KeySpec {}

                            impl Debug for KeySpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for KeySpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        KeySpec::RSA_2048 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__2048")?;
                                            Ok(())
                                        }
                                        KeySpec::RSA_3072 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__3072")?;
                                            Ok(())
                                        }
                                        KeySpec::RSA_4096 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__4096")?;
                                            Ok(())
                                        }
                                        KeySpec::ECC_NIST_P256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P256")?;
                                            Ok(())
                                        }
                                        KeySpec::ECC_NIST_P384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P384")?;
                                            Ok(())
                                        }
                                        KeySpec::ECC_NIST_P521 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P521")?;
                                            Ok(())
                                        }
                                        KeySpec::ECC_SECG_P256K1 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__SECG__P256K1")?;
                                            Ok(())
                                        }
                                        KeySpec::SYMMETRIC_DEFAULT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.SYMMETRIC__DEFAULT")?;
                                            Ok(())
                                        }
                                        KeySpec::HMAC_224 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__224")?;
                                            Ok(())
                                        }
                                        KeySpec::HMAC_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__256")?;
                                            Ok(())
                                        }
                                        KeySpec::HMAC_384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__384")?;
                                            Ok(())
                                        }
                                        KeySpec::HMAC_512 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__512")?;
                                            Ok(())
                                        }
                                        KeySpec::SM2 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.SM2")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for KeySpec {}

                            impl Hash for KeySpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        KeySpec::RSA_2048 {} => {}
                                        KeySpec::RSA_3072 {} => {}
                                        KeySpec::RSA_4096 {} => {}
                                        KeySpec::ECC_NIST_P256 {} => {}
                                        KeySpec::ECC_NIST_P384 {} => {}
                                        KeySpec::ECC_NIST_P521 {} => {}
                                        KeySpec::ECC_SECG_P256K1 {} => {}
                                        KeySpec::SYMMETRIC_DEFAULT {} => {}
                                        KeySpec::HMAC_224 {} => {}
                                        KeySpec::HMAC_256 {} => {}
                                        KeySpec::HMAC_384 {} => {}
                                        KeySpec::HMAC_512 {} => {}
                                        KeySpec::SM2 {} => {}
                                    }
                                }
                            }

                            impl Default for KeySpec {
                                fn default() -> KeySpec {
                                    KeySpec::RSA_2048 {}
                                }
                            }

                            impl AsRef<KeySpec> for &KeySpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum KeyUsageType {
                                SIGN_VERIFY {},
                                ENCRYPT_DECRYPT {},
                                GENERATE_VERIFY_MAC {},
                                KEY_AGREEMENT {},
                            }

                            impl KeyUsageType {}

                            impl Debug for KeyUsageType {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for KeyUsageType {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        KeyUsageType::SIGN_VERIFY {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.SIGN__VERIFY")?;
                                            Ok(())
                                        }
                                        KeyUsageType::ENCRYPT_DECRYPT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.ENCRYPT__DECRYPT")?;
                                            Ok(())
                                        }
                                        KeyUsageType::GENERATE_VERIFY_MAC {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.GENERATE__VERIFY__MAC")?;
                                            Ok(())
                                        }
                                        KeyUsageType::KEY_AGREEMENT {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.KEY__AGREEMENT")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for KeyUsageType {}

                            impl Hash for KeyUsageType {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        KeyUsageType::SIGN_VERIFY {} => {}
                                        KeyUsageType::ENCRYPT_DECRYPT {} => {}
                                        KeyUsageType::GENERATE_VERIFY_MAC {} => {}
                                        KeyUsageType::KEY_AGREEMENT {} => {}
                                    }
                                }
                            }

                            impl Default for KeyUsageType {
                                fn default() -> KeyUsageType {
                                    KeyUsageType::SIGN_VERIFY {}
                                }
                            }

                            impl AsRef<KeyUsageType> for &KeyUsageType {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type NumberOfBytesType = i32;

                            #[derive(PartialEq, Clone)]
                            pub enum OriginType {
                                AWS_KMS {},
                                EXTERNAL {},
                                AWS_CLOUDHSM {},
                                EXTERNAL_KEY_STORE {},
                            }

                            impl OriginType {}

                            impl Debug for OriginType {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for OriginType {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        OriginType::AWS_KMS {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.AWS__KMS")?;
                                            Ok(())
                                        }
                                        OriginType::EXTERNAL {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.EXTERNAL")?;
                                            Ok(())
                                        }
                                        OriginType::AWS_CLOUDHSM {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.AWS__CLOUDHSM")?;
                                            Ok(())
                                        }
                                        OriginType::EXTERNAL_KEY_STORE {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.EXTERNAL__KEY__STORE")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for OriginType {}

                            impl Hash for OriginType {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        OriginType::AWS_KMS {} => {}
                                        OriginType::EXTERNAL {} => {}
                                        OriginType::AWS_CLOUDHSM {} => {}
                                        OriginType::EXTERNAL_KEY_STORE {} => {}
                                    }
                                }
                            }

                            impl Default for OriginType {
                                fn default() -> OriginType {
                                    OriginType::AWS_KMS {}
                                }
                            }

                            impl AsRef<OriginType> for &OriginType {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type PlaintextType = ::dafny_runtime::Sequence<u8>;

                            pub type PublicKeyType = ::dafny_runtime::Sequence<u8>;

                            #[derive(PartialEq, Clone)]
                            pub enum RecipientInfo {
                                RecipientInfo {
                  KeyEncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyEncryptionMechanism>>>,
                  AttestationDocument: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::AttestationDocumentType>>
                }
              }

                            impl RecipientInfo {
                                pub fn KeyEncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::KeyEncryptionMechanism>>>{
                                    match self {
                                        RecipientInfo::RecipientInfo {
                                            KeyEncryptionAlgorithm,
                                            AttestationDocument,
                                        } => KeyEncryptionAlgorithm,
                                    }
                                }
                                pub fn AttestationDocument(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::AttestationDocumentType>>{
                                    match self {
                                        RecipientInfo::RecipientInfo {
                                            KeyEncryptionAlgorithm,
                                            AttestationDocument,
                                        } => AttestationDocument,
                                    }
                                }
                            }

                            impl Debug for RecipientInfo {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for RecipientInfo {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        RecipientInfo::RecipientInfo {
                                            KeyEncryptionAlgorithm,
                                            AttestationDocument,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.RecipientInfo.RecipientInfo(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyEncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                AttestationDocument,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for RecipientInfo {}

                            impl Hash for RecipientInfo {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        RecipientInfo::RecipientInfo {
                                            KeyEncryptionAlgorithm,
                                            AttestationDocument,
                                        } => {
                                            ::std::hash::Hash::hash(KeyEncryptionAlgorithm, _state);
                                            ::std::hash::Hash::hash(AttestationDocument, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for RecipientInfo {
                                fn default() -> RecipientInfo {
                                    RecipientInfo::RecipientInfo {
                                        KeyEncryptionAlgorithm: ::std::default::Default::default(),
                                        AttestationDocument: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<RecipientInfo> for &RecipientInfo {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ReEncryptRequest {
                                ReEncryptRequest {
                  CiphertextBlob: crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType,
                  SourceEncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  SourceKeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  DestinationKeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                  DestinationEncryptionContext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
                  SourceEncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  DestinationEncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  GrantTokens: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>,
                  DryRun: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                }
              }

                            impl ReEncryptRequest {
                                pub fn CiphertextBlob(&self) -> &crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType{
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => CiphertextBlob,
                                    }
                                }
                                pub fn SourceEncryptionContext(
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
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => SourceEncryptionContext,
                                    }
                                }
                                pub fn SourceKeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => SourceKeyId,
                                    }
                                }
                                pub fn DestinationKeyId(
                                    &self,
                                ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>
                                {
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => DestinationKeyId,
                                    }
                                }
                                pub fn DestinationEncryptionContext(
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
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => DestinationEncryptionContext,
                                    }
                                }
                                pub fn SourceEncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => SourceEncryptionAlgorithm,
                                    }
                                }
                                pub fn DestinationEncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => DestinationEncryptionAlgorithm,
                                    }
                                }
                                pub fn GrantTokens(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>>{
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => GrantTokens,
                                    }
                                }
                                pub fn DryRun(
                                    &self,
                                ) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<bool>>
                                {
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => DryRun,
                                    }
                                }
                            }

                            impl Debug for ReEncryptRequest {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ReEncryptRequest {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest.ReEncryptRequest(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextBlob,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SourceEncryptionContext,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SourceKeyId,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DestinationKeyId,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DestinationEncryptionContext,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SourceEncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DestinationEncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                GrantTokens,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DryRun, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ReEncryptRequest {}

                            impl Hash for ReEncryptRequest {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ReEncryptRequest::ReEncryptRequest {
                                            CiphertextBlob,
                                            SourceEncryptionContext,
                                            SourceKeyId,
                                            DestinationKeyId,
                                            DestinationEncryptionContext,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                            GrantTokens,
                                            DryRun,
                                        } => {
                                            ::std::hash::Hash::hash(CiphertextBlob, _state);
                                            ::std::hash::Hash::hash(
                                                SourceEncryptionContext,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(SourceKeyId, _state);
                                            ::std::hash::Hash::hash(DestinationKeyId, _state);
                                            ::std::hash::Hash::hash(
                                                DestinationEncryptionContext,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                SourceEncryptionAlgorithm,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                DestinationEncryptionAlgorithm,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(GrantTokens, _state);
                                            ::std::hash::Hash::hash(DryRun, _state)
                                        }
                                    }
                                }
                            }

                            impl Default for ReEncryptRequest {
                                fn default() -> ReEncryptRequest {
                                    ReEncryptRequest::ReEncryptRequest {
                                        CiphertextBlob: ::std::default::Default::default(),
                                        SourceEncryptionContext: ::std::default::Default::default(),
                                        SourceKeyId: ::std::default::Default::default(),
                                        DestinationKeyId: ::std::default::Default::default(),
                                        DestinationEncryptionContext:
                                            ::std::default::Default::default(),
                                        SourceEncryptionAlgorithm: ::std::default::Default::default(
                                        ),
                                        DestinationEncryptionAlgorithm:
                                            ::std::default::Default::default(),
                                        GrantTokens: ::std::default::Default::default(),
                                        DryRun: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ReEncryptRequest> for &ReEncryptRequest {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum ReEncryptResponse {
                                ReEncryptResponse {
                  CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>,
                  SourceKeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  KeyId: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
                  SourceEncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>,
                  DestinationEncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>
                }
              }

                            impl ReEncryptResponse {
                                pub fn CiphertextBlob(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>>{
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => CiphertextBlob,
                                    }
                                }
                                pub fn SourceKeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => SourceKeyId,
                                    }
                                }
                                pub fn KeyId(
                                    &self,
                                ) -> &::std::rc::Rc<
                                    crate::r#_Wrappers_Compile::Option<
                                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                                    >,
                                > {
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => KeyId,
                                    }
                                }
                                pub fn SourceEncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => SourceEncryptionAlgorithm,
                                    }
                                }
                                pub fn DestinationEncryptionAlgorithm(&self) -> &::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>>{
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => DestinationEncryptionAlgorithm,
                                    }
                                }
                            }

                            impl Debug for ReEncryptResponse {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for ReEncryptResponse {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse.ReEncryptResponse(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                CiphertextBlob,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SourceKeyId,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                KeyId, _formatter, false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                SourceEncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ", ")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                DestinationEncryptionAlgorithm,
                                                _formatter,
                                                false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for ReEncryptResponse {}

                            impl Hash for ReEncryptResponse {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        ReEncryptResponse::ReEncryptResponse {
                                            CiphertextBlob,
                                            SourceKeyId,
                                            KeyId,
                                            SourceEncryptionAlgorithm,
                                            DestinationEncryptionAlgorithm,
                                        } => {
                                            ::std::hash::Hash::hash(CiphertextBlob, _state);
                                            ::std::hash::Hash::hash(SourceKeyId, _state);
                                            ::std::hash::Hash::hash(KeyId, _state);
                                            ::std::hash::Hash::hash(
                                                SourceEncryptionAlgorithm,
                                                _state,
                                            );
                                            ::std::hash::Hash::hash(
                                                DestinationEncryptionAlgorithm,
                                                _state,
                                            )
                                        }
                                    }
                                }
                            }

                            impl Default for ReEncryptResponse {
                                fn default() -> ReEncryptResponse {
                                    ReEncryptResponse::ReEncryptResponse {
                                        CiphertextBlob: ::std::default::Default::default(),
                                        SourceKeyId: ::std::default::Default::default(),
                                        KeyId: ::std::default::Default::default(),
                                        SourceEncryptionAlgorithm: ::std::default::Default::default(
                                        ),
                                        DestinationEncryptionAlgorithm:
                                            ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<ReEncryptResponse> for &ReEncryptResponse {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum SigningAlgorithmSpec {
                                RSASSA_PSS_SHA_256 {},
                                RSASSA_PSS_SHA_384 {},
                                RSASSA_PSS_SHA_512 {},
                                RSASSA_PKCS1_V1_5_SHA_256 {},
                                RSASSA_PKCS1_V1_5_SHA_384 {},
                                RSASSA_PKCS1_V1_5_SHA_512 {},
                                ECDSA_SHA_256 {},
                                ECDSA_SHA_384 {},
                                ECDSA_SHA_512 {},
                                SM2DSA {},
                            }

                            impl SigningAlgorithmSpec {}

                            impl Debug for SigningAlgorithmSpec {
                                fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                                    ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
                                }
                            }

                            impl DafnyPrint for SigningAlgorithmSpec {
                                fn fmt_print(
                                    &self,
                                    _formatter: &mut ::std::fmt::Formatter,
                                    _in_seq: bool,
                                ) -> std::fmt::Result {
                                    match self {
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__256")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__384")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__512")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__256")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__384")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__512")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::ECDSA_SHA_256 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__256")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::ECDSA_SHA_384 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__384")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::ECDSA_SHA_512 {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__512")?;
                                            Ok(())
                                        }
                                        SigningAlgorithmSpec::SM2DSA {} => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.SM2DSA")?;
                                            Ok(())
                                        }
                                    }
                                }
                            }

                            impl Eq for SigningAlgorithmSpec {}

                            impl Hash for SigningAlgorithmSpec {
                                fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
                                    match self {
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {} => {}
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {} => {}
                                        SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {} => {}
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {} => {}
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {} => {}
                                        SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {} => {}
                                        SigningAlgorithmSpec::ECDSA_SHA_256 {} => {}
                                        SigningAlgorithmSpec::ECDSA_SHA_384 {} => {}
                                        SigningAlgorithmSpec::ECDSA_SHA_512 {} => {}
                                        SigningAlgorithmSpec::SM2DSA {} => {}
                                    }
                                }
                            }

                            impl Default for SigningAlgorithmSpec {
                                fn default() -> SigningAlgorithmSpec {
                                    SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {}
                                }
                            }

                            impl AsRef<SigningAlgorithmSpec> for &SigningAlgorithmSpec {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub struct IKMSClientCallHistory {}

                            impl IKMSClientCallHistory {
                                pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
                                    ::dafny_runtime::allocate_object::<Self>()
                                }
                            }

                            impl UpcastObject<dyn Any>
                for crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClientCallHistory {
                ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
              }

                            pub trait IKMSClient:
                                ::std::any::Any
                                + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
                            {
                                fn Decrypt(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn DeriveSharedSecret(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn Encrypt(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn GenerateDataKey(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn GenerateDataKeyWithoutPlaintext(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn GetPublicKey(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                                fn ReEncrypt(&mut self, input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptRequest>) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>;
                            }

                            #[derive(PartialEq, Clone)]
                            pub enum Error {
                                DependencyTimeoutException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                DisabledException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                DryRunOperationException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                IncorrectKeyException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InvalidArnException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InvalidCiphertextException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InvalidGrantTokenException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                InvalidKeyUsageException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                KeyUnavailableException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                KMSInternalException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                KMSInvalidStateException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                NotFoundException {
                                    message: ::std::rc::Rc<
                                        crate::r#_Wrappers_Compile::Option<
                                            ::dafny_runtime::Sequence<
                                                ::dafny_runtime::DafnyCharUTF16,
                                            >,
                                        >,
                                    >,
                                },
                                UnsupportedOperationException {
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
                                        Error::DependencyTimeoutException { message } => message,
                                        Error::DisabledException { message } => message,
                                        Error::DryRunOperationException { message } => message,
                                        Error::IncorrectKeyException { message } => message,
                                        Error::InvalidArnException { message } => message,
                                        Error::InvalidCiphertextException { message } => message,
                                        Error::InvalidGrantTokenException { message } => message,
                                        Error::InvalidKeyUsageException { message } => message,
                                        Error::KeyUnavailableException { message } => message,
                                        Error::KMSInternalException { message } => message,
                                        Error::KMSInvalidStateException { message } => message,
                                        Error::NotFoundException { message } => message,
                                        Error::UnsupportedOperationException { message } => message,
                                        Error::Opaque { obj } => {
                                            panic!("field does not exist on this variant")
                                        }
                                    }
                                }
                                pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
                                    match self {
                                        Error::DependencyTimeoutException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::DisabledException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::DryRunOperationException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::IncorrectKeyException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidArnException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidCiphertextException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidGrantTokenException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::InvalidKeyUsageException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::KeyUnavailableException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::KMSInternalException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::KMSInvalidStateException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::NotFoundException { message } => {
                                            panic!("field does not exist on this variant")
                                        }
                                        Error::UnsupportedOperationException { message } => {
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
                                        Error::DependencyTimeoutException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DependencyTimeoutException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::DisabledException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DisabledException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::DryRunOperationException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DryRunOperationException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::IncorrectKeyException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.IncorrectKeyException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InvalidArnException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidArnException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InvalidCiphertextException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidCiphertextException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InvalidGrantTokenException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidGrantTokenException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::InvalidKeyUsageException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidKeyUsageException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::KeyUnavailableException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KeyUnavailableException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::KMSInternalException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KMSInternalException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::KMSInvalidStateException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KMSInvalidStateException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::NotFoundException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.NotFoundException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::UnsupportedOperationException { message } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.UnsupportedOperationException(")?;
                                            ::dafny_runtime::DafnyPrint::fmt_print(
                                                message, _formatter, false,
                                            )?;
                                            write!(_formatter, ")")?;
                                            Ok(())
                                        }
                                        Error::Opaque { obj } => {
                                            write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.Opaque(")?;
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
                                        Error::DependencyTimeoutException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::DisabledException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::DryRunOperationException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::IncorrectKeyException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InvalidArnException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InvalidCiphertextException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InvalidGrantTokenException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::InvalidKeyUsageException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::KeyUnavailableException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::KMSInternalException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::KMSInvalidStateException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::NotFoundException { message } => {
                                            ::std::hash::Hash::hash(message, _state)
                                        }
                                        Error::UnsupportedOperationException { message } => {
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
                                    Error::DependencyTimeoutException {
                                        message: ::std::default::Default::default(),
                                    }
                                }
                            }

                            impl AsRef<Error> for &Error {
                                fn as_ref(&self) -> Self {
                                    self
                                }
                            }

                            pub type OpaqueError = ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>;
                        }
                    }
                }
            }
        }
    }
}
pub mod r#_Com_Compile {
    pub mod r#_Amazonaws_Compile {}
}
pub mod r#_TestComAmazonawsKms_Compile {
    pub struct _default {}

    impl _default {
        pub fn workAround(literal: &::dafny_runtime::Sequence<u8>) -> crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType{
            literal.clone()
        }
        pub fn BasicDecryptTests() -> () {
            let mut CiphertextBlob: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![
                1, 1, 1, 0, 120, 64, 243, 140, 39, 94, 49, 9, 116, 22, 193, 7, 41, 81, 80, 87, 25,
                100, 173, 163, 239, 28, 33, 233, 76, 139, 160, 189, 188, 157, 15, 180, 20, 0, 0, 0,
                98, 48, 96, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 6, 160, 83, 48, 81, 2, 1, 0, 48,
                76, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 1, 48, 30, 6, 9, 96, 134, 72, 1, 101, 3,
                4, 1, 46, 48, 17, 4, 12, 196, 249, 60, 7, 21, 231, 87, 70, 216, 12, 31, 13, 2, 1,
                16, 128, 31, 222, 119, 162, 112, 88, 153, 39, 197, 21, 182, 116, 176, 120, 174,
                107, 82, 182, 223, 160, 201, 15, 29, 3, 254, 3, 208, 72, 171, 64, 207, 175
            ];
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(&::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest::DecryptRequest {
            CiphertextBlob: crate::r#_TestComAmazonawsKms_Compile::_default::workAround(&CiphertextBlob),
            EncryptionContext: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            GrantTokens: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>::None {}),
            KeyId: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: crate::r#_TestComAmazonawsKms_Compile::_default::keyId()
                }),
            EncryptionAlgorithm: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>::None {}),
            Recipient: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
          }), &::dafny_runtime::seq![165, 191, 67, 62], &crate::r#_TestComAmazonawsKms_Compile::_default::keyId());
            return ();
        }
        pub fn BasicGenerateTests() -> () {
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicGenerateTest(&::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest::GenerateDataKeyRequest {
            KeyId: crate::r#_TestComAmazonawsKms_Compile::_default::keyId(),
            EncryptionContext: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            NumberOfBytes: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<crate::software::amazon::cryptography::services::kms::internaldafny::types::NumberOfBytesType>::Some {
                  value: 32
                }),
            KeySpec: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DataKeySpec>>::None {}),
            GrantTokens: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>::None {}),
            Recipient: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
          }));
            return ();
        }
        pub fn BasicEncryptTests() -> () {
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicEncryptTest(&::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest::EncryptRequest {
            KeyId: crate::r#_TestComAmazonawsKms_Compile::_default::keyId(),
            Plaintext: ::dafny_runtime::seq![97, 115, 100, 102],
            EncryptionContext: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            GrantTokens: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<crate::software::amazon::cryptography::services::kms::internaldafny::types::GrantTokenList>::None {}),
            EncryptionAlgorithm: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>::None {}),
            DryRun: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
          }));
            return ();
        }
        pub fn BasicDecryptTest(
            input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest>,
            expectedPlaintext: &crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType,
            expectedKeyId: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient::Decrypt(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !matches!(
                (&ret.read()).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs0: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse> = ret.read().value().clone();
            let mut KeyId: ::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs0.KeyId().clone();
            let mut Plaintext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>> = r#__let_tmp_rhs0.Plaintext().clone();
            let mut EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>> = r#__let_tmp_rhs0.EncryptionAlgorithm().clone();
            let mut CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>> = r#__let_tmp_rhs0.CiphertextForRecipient().clone();
            if !matches!(
                (&Plaintext).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e00: crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType = Plaintext.value().clone();
            let mut _e10: crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType = expectedPlaintext.clone();
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
            let mut _e01: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                KeyId.value().clone();
            let mut _e11: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                expectedKeyId.clone();
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
            return ();
        }
        pub fn BasicGenerateTest(
            input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient::GenerateDataKey(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !matches!(
                (&ret.read()).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs1: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse> = ret.read().value().clone();
            let mut CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>> = r#__let_tmp_rhs1.CiphertextBlob().clone();
            let mut Plaintext: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::PlaintextType>> = r#__let_tmp_rhs1.Plaintext().clone();
            let mut KeyId: ::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs1.KeyId().clone();
            let mut CiphertextForRecipient: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>> = r#__let_tmp_rhs1.CiphertextForRecipient().clone();
            if !matches!(
                (&CiphertextBlob).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&Plaintext).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut _e02: ::dafny_runtime::DafnyInt = Plaintext.value().cardinality();
            let mut _e12: ::dafny_runtime::_System::nat =
                ::std::convert::Into::<::dafny_runtime::DafnyInt>::into(
                    input.NumberOfBytes().value().clone(),
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
            let mut decryptInput: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest> = ::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest::DecryptRequest {
            CiphertextBlob: CiphertextBlob.value().clone(),
            EncryptionContext: input.EncryptionContext().clone(),
            GrantTokens: input.GrantTokens().clone(),
            KeyId: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: KeyId.value().clone()
                }),
            EncryptionAlgorithm: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>::None {}),
            Recipient: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
          });
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(
                &decryptInput,
                Plaintext.value(),
                input.KeyId(),
            );
            return ();
        }
        pub fn BasicEncryptTest(
            input: &::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<crate::r#_Wrappers_Compile::Result<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse>, ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(crate::software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient::Encrypt(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !matches!(
                (&ret.read()).as_ref(),
                crate::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs2: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse> = ret.read().value().clone();
            let mut CiphertextBlob: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<crate::software::amazon::cryptography::services::kms::internaldafny::types::CiphertextType>> = r#__let_tmp_rhs2.CiphertextBlob().clone();
            let mut KeyId: ::std::rc::Rc<
                crate::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs2.KeyId().clone();
            let mut EncryptionAlgorithm: ::std::rc::Rc<crate::r#_Wrappers_Compile::Option<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::EncryptionAlgorithmSpec>>> = r#__let_tmp_rhs2.EncryptionAlgorithm().clone();
            if !matches!(
                (&CiphertextBlob).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                crate::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut decryptInput: ::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest> = ::std::rc::Rc::new(crate::software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest::DecryptRequest {
            CiphertextBlob: CiphertextBlob.value().clone(),
            EncryptionContext: input.EncryptionContext().clone(),
            GrantTokens: input.GrantTokens().clone(),
            KeyId: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: KeyId.value().clone()
                }),
            EncryptionAlgorithm: input.EncryptionAlgorithm().clone(),
            Recipient: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<::std::rc::Rc<crate::software::amazon::cryptography::services::kms::internaldafny::types::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(crate::r#_Wrappers_Compile::Option::<bool>::None {})
          });
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(
                &decryptInput,
                input.Plaintext(),
                input.KeyId(),
            );
            return ();
        }
        pub fn keyId() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of(
                "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f",
            )
        }
        pub fn TEST_REGION() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of("us-west-2")
        }
    }

    #[test]
    pub fn BasicDecryptTests() {
        _default::BasicDecryptTests()
    }

    #[test]
    pub fn BasicGenerateTests() {
        _default::BasicGenerateTests()
    }

    #[test]
    pub fn BasicEncryptTests() {
        _default::BasicEncryptTests()
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
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicDecryptTests: "#
                ))
            );
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicGenerateTests: "#
                ))
            );
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicGenerateTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicEncryptTests: "#
                ))
            );
            crate::r#_TestComAmazonawsKms_Compile::_default::BasicEncryptTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }
}
fn main() {
    _module::_default::_Test__Main_();
}
