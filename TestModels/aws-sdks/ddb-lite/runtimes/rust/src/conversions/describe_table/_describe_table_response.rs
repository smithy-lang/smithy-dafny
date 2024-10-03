// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::describe_table::DescribeTableOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableOutput::DescribeTableOutput {
        Table: ::std::rc::Rc::new(match &value.table {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::table_description::to_dafny(&x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 
