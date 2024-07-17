// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::Condition,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Condition>{
  ::std::rc::Rc::new(
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Condition::Condition {
        AttributeValueList: todo!(),
 ComparisonOperator: ::std::rc::Rc::new(match &value.comparison_operator {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::comparison_operator::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Condition,
    >,
) -> aws_sdk_dynamodb::types::Condition {
    aws_sdk_dynamodb::types::Condition::builder()
          .set_attribute_value_list(todo!())
 .set_comparison_operator(Some( crate::conversions::comparison_operator::from_dafny(dafny_value.ComparisonOperator()) ))
          .build()
}
