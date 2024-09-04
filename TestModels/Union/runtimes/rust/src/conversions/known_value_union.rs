// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::KnownValueUnion,
) -> ::std::rc::Rc<
    crate::r#simple::union::internaldafny::types::KnownValueUnion,
> {
    ::std::rc::Rc::new(match value {
        crate::types::KnownValueUnion::Value(x) =>
    crate::r#simple::union::internaldafny::types::KnownValueUnion::Value {
        Value: x.clone(),
    },
        crate::types::KnownValueUnion::Unknown => unreachable!(),
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::union::internaldafny::types::KnownValueUnion,
    >,
) -> crate::types::KnownValueUnion {
    match &::std::rc::Rc::unwrap_or_clone(dafny_value) {
        crate::r#simple::union::internaldafny::types::KnownValueUnion::Value {
    Value: x @ _,
} => crate::types::KnownValueUnion::Value(x .clone()),
    }
}
