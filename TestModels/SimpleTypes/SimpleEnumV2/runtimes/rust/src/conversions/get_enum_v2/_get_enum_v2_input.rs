// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_enum_v2::GetEnumV2Input,
) -> ::std::rc::Rc<
    crate::r#simple::types::enumv2::internaldafny::types::GetEnumV2Input,
>{
    ::std::rc::Rc::new(crate::r#simple::types::enumv2::internaldafny::types::GetEnumV2Input::GetEnumV2Input {
        value: ::std::rc::Rc::new(match &value.value {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::simple_enum_v2_shape::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::enumv2::internaldafny::types::GetEnumV2Input,
    >,
) -> crate::operation::get_enum_v2::GetEnumV2Input {
    crate::operation::get_enum_v2::GetEnumV2Input::builder()
        .set_value(match &**dafny_value.value() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::simple_enum_v2_shape::from_dafny(value)
    ),
    _ => None,
}
)
        .build()
        .unwrap()
}
