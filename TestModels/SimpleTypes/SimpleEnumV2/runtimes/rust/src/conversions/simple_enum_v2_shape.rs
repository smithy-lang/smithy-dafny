// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::SimpleEnumV2Shape,
) -> ::std::rc::Rc<crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape>{
    ::std::rc::Rc::new(match value {
        crate::types::SimpleEnumV2Shape::First => crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::FIRST {},
crate::types::SimpleEnumV2Shape::Second => crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::SECOND {},
crate::types::SimpleEnumV2Shape::Third => crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::THIRD {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape,
) -> crate::types::SimpleEnumV2Shape {
    match dafny_value {
        crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::FIRST {} => crate::types::SimpleEnumV2Shape::First,
crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::SECOND {} => crate::types::SimpleEnumV2Shape::Second,
crate::r#simple::types::enumv2::internaldafny::types::SimpleEnumV2Shape::THIRD {} => crate::types::SimpleEnumV2Shape::Third,
    }
}
