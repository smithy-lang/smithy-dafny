// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::ConditionalOperator,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator>{
    ::std::rc::Rc::new(match value {
 aws_sdk_dynamodb::types::ConditionalOperator::And => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator::AND {},
 aws_sdk_dynamodb::types::ConditionalOperator::Or => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator::OR {},
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
    dafny_value: &crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator,
) -> aws_sdk_dynamodb::types::ConditionalOperator {
    match dafny_value {
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator::AND {} => aws_sdk_dynamodb::types::ConditionalOperator::And,
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConditionalOperator::OR {} => aws_sdk_dynamodb::types::ConditionalOperator::Or,
    }
}
