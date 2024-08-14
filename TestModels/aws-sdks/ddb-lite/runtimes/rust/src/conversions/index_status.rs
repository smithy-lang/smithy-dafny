// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_dynamodb::types::IndexStatus,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus>{
    ::std::rc::Rc::new(match value {
 aws_sdk_dynamodb::types::IndexStatus::Creating => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::CREATING {},
 aws_sdk_dynamodb::types::IndexStatus::Updating => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::UPDATING {},
 aws_sdk_dynamodb::types::IndexStatus::Deleting => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::DELETING {},
 aws_sdk_dynamodb::types::IndexStatus::Active => crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::ACTIVE {},
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
    dafny_value: &crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus,
) -> aws_sdk_dynamodb::types::IndexStatus {
    match dafny_value {
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::CREATING {} => aws_sdk_dynamodb::types::IndexStatus::Creating,
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::UPDATING {} => aws_sdk_dynamodb::types::IndexStatus::Updating,
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::DELETING {} => aws_sdk_dynamodb::types::IndexStatus::Deleting,
 crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IndexStatus::ACTIVE {} => aws_sdk_dynamodb::types::IndexStatus::Active,
    }
}
