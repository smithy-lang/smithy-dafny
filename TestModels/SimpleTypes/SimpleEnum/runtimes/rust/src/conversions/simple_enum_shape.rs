// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::SimpleEnumShape,
) -> ::std::rc::Rc<crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape>{
    ::std::rc::Rc::new(match value {
        crate::types::SimpleEnumShape::First => crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {},
crate::types::SimpleEnumShape::Second => crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {},
crate::types::SimpleEnumShape::Third => crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape,
) -> crate::types::SimpleEnumShape {
    match dafny_value {
        crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::FIRST {} => crate::types::SimpleEnumShape::First,
crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::SECOND {} => crate::types::SimpleEnumShape::Second,
crate::r#simple::types::smithyenum::internaldafny::types::SimpleEnumShape::THIRD {} => crate::types::SimpleEnumShape::Third,
    }
}
