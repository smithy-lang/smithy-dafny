// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::ComparisonOperator,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator>{
    ::std::rc::Rc::new(match value {
 aws_sdk_dynamodb::types::ComparisonOperator::Eq => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::EQ {},
 aws_sdk_dynamodb::types::ComparisonOperator::Ne => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NE {},
 aws_sdk_dynamodb::types::ComparisonOperator::In => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::IN {},
 aws_sdk_dynamodb::types::ComparisonOperator::Le => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::LE {},
 aws_sdk_dynamodb::types::ComparisonOperator::Lt => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::LT {},
 aws_sdk_dynamodb::types::ComparisonOperator::Ge => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::GE {},
 aws_sdk_dynamodb::types::ComparisonOperator::Gt => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::GT {},
 aws_sdk_dynamodb::types::ComparisonOperator::Between => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::BETWEEN {},
 aws_sdk_dynamodb::types::ComparisonOperator::NotNull => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NOT_NULL {},
 aws_sdk_dynamodb::types::ComparisonOperator::Null => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NULL {},
 aws_sdk_dynamodb::types::ComparisonOperator::Contains => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::CONTAINS {},
 aws_sdk_dynamodb::types::ComparisonOperator::NotContains => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NOT_CONTAINS {},
 aws_sdk_dynamodb::types::ComparisonOperator::BeginsWith => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::BEGINS_WITH {},
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
    dafny_value: &crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator,
) -> aws_sdk_dynamodb::types::ComparisonOperator {
    match dafny_value {
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::EQ {} => aws_sdk_dynamodb::types::ComparisonOperator::Eq,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NE {} => aws_sdk_dynamodb::types::ComparisonOperator::Ne,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::IN {} => aws_sdk_dynamodb::types::ComparisonOperator::In,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::LE {} => aws_sdk_dynamodb::types::ComparisonOperator::Le,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::LT {} => aws_sdk_dynamodb::types::ComparisonOperator::Lt,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::GE {} => aws_sdk_dynamodb::types::ComparisonOperator::Ge,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::GT {} => aws_sdk_dynamodb::types::ComparisonOperator::Gt,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::BETWEEN {} => aws_sdk_dynamodb::types::ComparisonOperator::Between,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NOT_NULL {} => aws_sdk_dynamodb::types::ComparisonOperator::NotNull,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NULL {} => aws_sdk_dynamodb::types::ComparisonOperator::Null,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::CONTAINS {} => aws_sdk_dynamodb::types::ComparisonOperator::Contains,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::NOT_CONTAINS {} => aws_sdk_dynamodb::types::ComparisonOperator::NotContains,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ComparisonOperator::BEGINS_WITH {} => aws_sdk_dynamodb::types::ComparisonOperator::BeginsWith,
    }
}
