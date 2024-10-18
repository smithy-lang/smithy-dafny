// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::WidgetType,
) -> ::std::rc::Rc<crate::r#simple::documentation::internaldafny::types::WidgetType>{
    ::std::rc::Rc::new(match value {
        crate::types::WidgetType::Blue => crate::r#simple::documentation::internaldafny::types::WidgetType::BLUE {},
crate::types::WidgetType::Large => crate::r#simple::documentation::internaldafny::types::WidgetType::LARGE {},
crate::types::WidgetType::Squishy => crate::r#simple::documentation::internaldafny::types::WidgetType::SQUISHY {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#simple::documentation::internaldafny::types::WidgetType,
) -> crate::types::WidgetType {
    match dafny_value {
        crate::r#simple::documentation::internaldafny::types::WidgetType::BLUE {} => crate::types::WidgetType::Blue,
crate::r#simple::documentation::internaldafny::types::WidgetType::LARGE {} => crate::types::WidgetType::Large,
crate::r#simple::documentation::internaldafny::types::WidgetType::SQUISHY {} => crate::types::WidgetType::Squishy,
    }
}
