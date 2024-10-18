// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::types::SomeKindOfThing,
) -> ::std::rc::Rc<
    crate::r#simple::documentation::internaldafny::types::SomeKindOfThing,
> {
    ::std::rc::Rc::new(match value {
        crate::types::SomeKindOfThing::Thing(x) =>
    crate::r#simple::documentation::internaldafny::types::SomeKindOfThing::thing {
        thing: crate::conversions::thing::to_dafny(&x.clone())
,
    },
crate::types::SomeKindOfThing::Widget(x) =>
    crate::r#simple::documentation::internaldafny::types::SomeKindOfThing::widget {
        widget: crate::conversions::widget::to_dafny(&x.clone())
,
    },
        _ => panic!("Unknown union variant: {:?}", value),
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::documentation::internaldafny::types::SomeKindOfThing,
    >,
) -> crate::types::SomeKindOfThing {
    match &::std::rc::Rc::unwrap_or_clone(dafny_value) {
        crate::r#simple::documentation::internaldafny::types::SomeKindOfThing::thing {
    thing: x @ _,
} => crate::types::SomeKindOfThing::Thing(crate::conversions::thing::from_dafny(x.clone())
),
crate::r#simple::documentation::internaldafny::types::SomeKindOfThing::widget {
    widget: x @ _,
} => crate::types::SomeKindOfThing::Widget(crate::conversions::widget::from_dafny(x.clone())
),
    }
}
