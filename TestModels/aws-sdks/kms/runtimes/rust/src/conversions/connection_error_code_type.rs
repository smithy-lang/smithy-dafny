// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::ConnectionErrorCodeType,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType>{
    ::std::rc::Rc::new(match value {
        aws_sdk_kms::types::ConnectionErrorCodeType::InvalidCredentials => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INVALID_CREDENTIALS {},
aws_sdk_kms::types::ConnectionErrorCodeType::ClusterNotFound => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::CLUSTER_NOT_FOUND {},
aws_sdk_kms::types::ConnectionErrorCodeType::NetworkErrors => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::NETWORK_ERRORS {},
aws_sdk_kms::types::ConnectionErrorCodeType::InternalError => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INTERNAL_ERROR {},
aws_sdk_kms::types::ConnectionErrorCodeType::InsufficientCloudhsmHsms => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INSUFFICIENT_CLOUDHSM_HSMS {},
aws_sdk_kms::types::ConnectionErrorCodeType::UserLockedOut => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_LOCKED_OUT {},
aws_sdk_kms::types::ConnectionErrorCodeType::UserNotFound => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_NOT_FOUND {},
aws_sdk_kms::types::ConnectionErrorCodeType::UserLoggedIn => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_LOGGED_IN {},
aws_sdk_kms::types::ConnectionErrorCodeType::SubnetNotFound => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::SUBNET_NOT_FOUND {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType,
) -> aws_sdk_kms::types::ConnectionErrorCodeType {
    match dafny_value {
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INVALID_CREDENTIALS {} => aws_sdk_kms::types::ConnectionErrorCodeType::InvalidCredentials,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::CLUSTER_NOT_FOUND {} => aws_sdk_kms::types::ConnectionErrorCodeType::ClusterNotFound,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::NETWORK_ERRORS {} => aws_sdk_kms::types::ConnectionErrorCodeType::NetworkErrors,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INTERNAL_ERROR {} => aws_sdk_kms::types::ConnectionErrorCodeType::InternalError,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::INSUFFICIENT_CLOUDHSM_HSMS {} => aws_sdk_kms::types::ConnectionErrorCodeType::InsufficientCloudhsmHsms,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_LOCKED_OUT {} => aws_sdk_kms::types::ConnectionErrorCodeType::UserLockedOut,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_NOT_FOUND {} => aws_sdk_kms::types::ConnectionErrorCodeType::UserNotFound,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::USER_LOGGED_IN {} => aws_sdk_kms::types::ConnectionErrorCodeType::UserLoggedIn,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectionErrorCodeType::SUBNET_NOT_FOUND {} => aws_sdk_kms::types::ConnectionErrorCodeType::SubnetNotFound,
    }
}
