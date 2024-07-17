// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::ReturnValue,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue>{
    ::std::rc::Rc::new(match value {
 aws_sdk_dynamodb::types::ReturnValue::None => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::NONE {},
 aws_sdk_dynamodb::types::ReturnValue::AllOld => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::ALL_OLD {},
 aws_sdk_dynamodb::types::ReturnValue::UpdatedOld => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::UPDATED_OLD {},
 aws_sdk_dynamodb::types::ReturnValue::AllNew => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::ALL_NEW {},
 aws_sdk_dynamodb::types::ReturnValue::UpdatedNew => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::UPDATED_NEW {},
        // TODO: This should not be a panic, but the Dafny image of the enum shape doesn't have an Unknown variant of any kind,
        // so there's no way to succeed.
        // See https://github.com/smithy-lang/smithy-dafny/issues/476.
        // This could be handled more cleanly if conversion functions returned Results,
        // but that would be a large and disruptive change to the overall code flow.
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue,
) -> aws_sdk_dynamodb::types::ReturnValue {
    match dafny_value {
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::NONE {} => aws_sdk_dynamodb::types::ReturnValue::None,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::ALL_OLD {} => aws_sdk_dynamodb::types::ReturnValue::AllOld,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::UPDATED_OLD {} => aws_sdk_dynamodb::types::ReturnValue::UpdatedOld,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::ALL_NEW {} => aws_sdk_dynamodb::types::ReturnValue::AllNew,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ReturnValue::UPDATED_NEW {} => aws_sdk_dynamodb::types::ReturnValue::UpdatedNew,
    }
}
