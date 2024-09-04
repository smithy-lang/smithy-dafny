// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::MyUnion,
) -> ::std::rc::Rc<
    crate::r#simple::union::internaldafny::types::MyUnion,
> {
    ::std::rc::Rc::new(match value {
        crate::types::MyUnion::IntegerValue(x) =>
    crate::r#simple::union::internaldafny::types::MyUnion::IntegerValue {
        IntegerValue: x.clone(),
    },
crate::types::MyUnion::StringValue(x) =>
    crate::r#simple::union::internaldafny::types::MyUnion::StringValue {
        StringValue: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&x),
    },
        crate::types::MyUnion::Unknown => unreachable!(),
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::union::internaldafny::types::MyUnion,
    >,
) -> crate::types::MyUnion {
    match &::std::rc::Rc::unwrap_or_clone(dafny_value) {
        crate::r#simple::union::internaldafny::types::MyUnion::IntegerValue {
    IntegerValue: x @ _,
} => crate::types::MyUnion::IntegerValue(x .clone()),
crate::r#simple::union::internaldafny::types::MyUnion::StringValue {
    StringValue: x @ _,
} => crate::types::MyUnion::StringValue(dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(x)),
    }
}
