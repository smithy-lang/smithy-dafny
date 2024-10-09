// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod already_exists_exception;

 pub mod cloud_hsm_cluster_in_use_exception;

 pub mod cloud_hsm_cluster_invalid_configuration_exception;

 pub mod cloud_hsm_cluster_not_active_exception;

 pub mod cloud_hsm_cluster_not_found_exception;

 pub mod cloud_hsm_cluster_not_related_exception;

 pub mod custom_key_store_has_cmks_exception;

 pub mod custom_key_store_invalid_state_exception;

 pub mod custom_key_store_name_in_use_exception;

 pub mod custom_key_store_not_found_exception;

 pub mod dependency_timeout_exception;

 pub mod disabled_exception;

 pub mod expired_import_token_exception;

 pub mod incorrect_key_exception;

 pub mod incorrect_key_material_exception;

 pub mod incorrect_trust_anchor_exception;

 pub mod invalid_alias_name_exception;

 pub mod invalid_arn_exception;

 pub mod invalid_ciphertext_exception;

 pub mod invalid_grant_id_exception;

 pub mod invalid_grant_token_exception;

 pub mod invalid_import_token_exception;

 pub mod invalid_key_usage_exception;

 pub mod invalid_marker_exception;

 pub mod key_unavailable_exception;

 pub mod kms_internal_exception;

 pub mod kms_invalid_signature_exception;

 pub mod kms_invalid_state_exception;

 pub mod limit_exceeded_exception;

 pub mod malformed_policy_document_exception;

 pub mod not_found_exception;

 pub mod tag_exception;

 pub mod unsupported_operation_exception;
 /// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
    ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque {
            obj: error_obj,
        },
    )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: ::dafny_runtime::DafnyType, E: 'static>(value: E) ->
    ::std::rc::Rc<
        crate::_Wrappers_Compile::Result<
            T,
            ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
        >
    >
{
    ::std::rc::Rc::new(crate::_Wrappers_Compile::Result::Failure {
        error: to_opaque_error(value),
    })
}
pub fn to_dafny(
    value: crate::types::error::Error,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
        crate::types::error::Error::CustomKeyStoreNotFoundException { error } =>
    crate::conversions::error::custom_key_store_not_found_exception::to_dafny(error),
crate::types::error::Error::CloudHsmClusterInUseException { error } =>
    crate::conversions::error::cloud_hsm_cluster_in_use_exception::to_dafny(error),
crate::types::error::Error::LimitExceededException { error } =>
    crate::conversions::error::limit_exceeded_exception::to_dafny(error),
crate::types::error::Error::KmsInternalException { error } =>
    crate::conversions::error::kms_internal_exception::to_dafny(error),
crate::types::error::Error::DisabledException { error } =>
    crate::conversions::error::disabled_exception::to_dafny(error),
crate::types::error::Error::InvalidGrantTokenException { error } =>
    crate::conversions::error::invalid_grant_token_exception::to_dafny(error),
crate::types::error::Error::IncorrectKeyMaterialException { error } =>
    crate::conversions::error::incorrect_key_material_exception::to_dafny(error),
crate::types::error::Error::IncorrectTrustAnchorException { error } =>
    crate::conversions::error::incorrect_trust_anchor_exception::to_dafny(error),
crate::types::error::Error::CloudHsmClusterNotActiveException { error } =>
    crate::conversions::error::cloud_hsm_cluster_not_active_exception::to_dafny(error),
crate::types::error::Error::KeyUnavailableException { error } =>
    crate::conversions::error::key_unavailable_exception::to_dafny(error),
crate::types::error::Error::NotFoundException { error } =>
    crate::conversions::error::not_found_exception::to_dafny(error),
crate::types::error::Error::InvalidAliasNameException { error } =>
    crate::conversions::error::invalid_alias_name_exception::to_dafny(error),
crate::types::error::Error::InvalidMarkerException { error } =>
    crate::conversions::error::invalid_marker_exception::to_dafny(error),
crate::types::error::Error::InvalidImportTokenException { error } =>
    crate::conversions::error::invalid_import_token_exception::to_dafny(error),
crate::types::error::Error::UnsupportedOperationException { error } =>
    crate::conversions::error::unsupported_operation_exception::to_dafny(error),
crate::types::error::Error::CloudHsmClusterNotRelatedException { error } =>
    crate::conversions::error::cloud_hsm_cluster_not_related_exception::to_dafny(error),
crate::types::error::Error::IncorrectKeyException { error } =>
    crate::conversions::error::incorrect_key_exception::to_dafny(error),
crate::types::error::Error::AlreadyExistsException { error } =>
    crate::conversions::error::already_exists_exception::to_dafny(error),
crate::types::error::Error::CustomKeyStoreNameInUseException { error } =>
    crate::conversions::error::custom_key_store_name_in_use_exception::to_dafny(error),
crate::types::error::Error::DependencyTimeoutException { error } =>
    crate::conversions::error::dependency_timeout_exception::to_dafny(error),
crate::types::error::Error::InvalidArnException { error } =>
    crate::conversions::error::invalid_arn_exception::to_dafny(error),
crate::types::error::Error::KmsInvalidStateException { error } =>
    crate::conversions::error::kms_invalid_state_exception::to_dafny(error),
crate::types::error::Error::ExpiredImportTokenException { error } =>
    crate::conversions::error::expired_import_token_exception::to_dafny(error),
crate::types::error::Error::CloudHsmClusterInvalidConfigurationException { error } =>
    crate::conversions::error::cloud_hsm_cluster_invalid_configuration_exception::to_dafny(error),
crate::types::error::Error::CustomKeyStoreHasCmKsException { error } =>
    crate::conversions::error::custom_key_store_has_cmks_exception::to_dafny(error),
crate::types::error::Error::KmsInvalidSignatureException { error } =>
    crate::conversions::error::kms_invalid_signature_exception::to_dafny(error),
crate::types::error::Error::InvalidKeyUsageException { error } =>
    crate::conversions::error::invalid_key_usage_exception::to_dafny(error),
crate::types::error::Error::InvalidGrantIdException { error } =>
    crate::conversions::error::invalid_grant_id_exception::to_dafny(error),
crate::types::error::Error::TagException { error } =>
    crate::conversions::error::tag_exception::to_dafny(error),
crate::types::error::Error::MalformedPolicyDocumentException { error } =>
    crate::conversions::error::malformed_policy_document_exception::to_dafny(error),
crate::types::error::Error::CustomKeyStoreInvalidStateException { error } =>
    crate::conversions::error::custom_key_store_invalid_state_exception::to_dafny(error),
crate::types::error::Error::CloudHsmClusterNotFoundException { error } =>
    crate::conversions::error::cloud_hsm_cluster_not_found_exception::to_dafny(error),
crate::types::error::Error::InvalidCiphertextException { error } =>
    crate::conversions::error::invalid_ciphertext_exception::to_dafny(error),
        crate::types::error::Error::Opaque { obj } =>
            ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            }),
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error,
    >,
) -> crate::types::error::Error {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CustomKeyStoreNotFoundException { message, .. } =>
  crate::types::error::Error::CustomKeyStoreNotFoundException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNotFoundException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CloudHsmClusterInUseException { message, .. } =>
  crate::types::error::Error::CloudHsmClusterInUseException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInUseException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::LimitExceededException { message, .. } =>
  crate::types::error::Error::LimitExceededException {
    error: aws_sdk_kms::types::error::LimitExceededException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KMSInternalException { message, .. } =>
  crate::types::error::Error::KmsInternalException {
    error: aws_sdk_kms::types::error::KmsInternalException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::DisabledException { message, .. } =>
  crate::types::error::Error::DisabledException {
    error: aws_sdk_kms::types::error::DisabledException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidGrantTokenException { message, .. } =>
  crate::types::error::Error::InvalidGrantTokenException {
    error: aws_sdk_kms::types::error::InvalidGrantTokenException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::IncorrectKeyMaterialException { message, .. } =>
  crate::types::error::Error::IncorrectKeyMaterialException {
    error: aws_sdk_kms::types::error::IncorrectKeyMaterialException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::IncorrectTrustAnchorException { message, .. } =>
  crate::types::error::Error::IncorrectTrustAnchorException {
    error: aws_sdk_kms::types::error::IncorrectTrustAnchorException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CloudHsmClusterNotActiveException { message, .. } =>
  crate::types::error::Error::CloudHsmClusterNotActiveException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotActiveException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KeyUnavailableException { message, .. } =>
  crate::types::error::Error::KeyUnavailableException {
    error: aws_sdk_kms::types::error::KeyUnavailableException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::NotFoundException { message, .. } =>
  crate::types::error::Error::NotFoundException {
    error: aws_sdk_kms::types::error::NotFoundException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidAliasNameException { message, .. } =>
  crate::types::error::Error::InvalidAliasNameException {
    error: aws_sdk_kms::types::error::InvalidAliasNameException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidMarkerException { message, .. } =>
  crate::types::error::Error::InvalidMarkerException {
    error: aws_sdk_kms::types::error::InvalidMarkerException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidImportTokenException { message, .. } =>
  crate::types::error::Error::InvalidImportTokenException {
    error: aws_sdk_kms::types::error::InvalidImportTokenException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::UnsupportedOperationException { message, .. } =>
  crate::types::error::Error::UnsupportedOperationException {
    error: aws_sdk_kms::types::error::UnsupportedOperationException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CloudHsmClusterNotRelatedException { message, .. } =>
  crate::types::error::Error::CloudHsmClusterNotRelatedException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotRelatedException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::IncorrectKeyException { message, .. } =>
  crate::types::error::Error::IncorrectKeyException {
    error: aws_sdk_kms::types::error::IncorrectKeyException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::AlreadyExistsException { message, .. } =>
  crate::types::error::Error::AlreadyExistsException {
    error: aws_sdk_kms::types::error::AlreadyExistsException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CustomKeyStoreNameInUseException { message, .. } =>
  crate::types::error::Error::CustomKeyStoreNameInUseException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNameInUseException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::DependencyTimeoutException { message, .. } =>
  crate::types::error::Error::DependencyTimeoutException {
    error: aws_sdk_kms::types::error::DependencyTimeoutException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidArnException { message, .. } =>
  crate::types::error::Error::InvalidArnException {
    error: aws_sdk_kms::types::error::InvalidArnException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KMSInvalidStateException { message, .. } =>
  crate::types::error::Error::KmsInvalidStateException {
    error: aws_sdk_kms::types::error::KmsInvalidStateException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::ExpiredImportTokenException { message, .. } =>
  crate::types::error::Error::ExpiredImportTokenException {
    error: aws_sdk_kms::types::error::ExpiredImportTokenException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CloudHsmClusterInvalidConfigurationException { message, .. } =>
  crate::types::error::Error::CloudHsmClusterInvalidConfigurationException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInvalidConfigurationException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CustomKeyStoreHasCMKsException { message, .. } =>
  crate::types::error::Error::CustomKeyStoreHasCmKsException {
    error: aws_sdk_kms::types::error::CustomKeyStoreHasCmKsException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KMSInvalidSignatureException { message, .. } =>
  crate::types::error::Error::KmsInvalidSignatureException {
    error: aws_sdk_kms::types::error::KmsInvalidSignatureException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidKeyUsageException { message, .. } =>
  crate::types::error::Error::InvalidKeyUsageException {
    error: aws_sdk_kms::types::error::InvalidKeyUsageException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidGrantIdException { message, .. } =>
  crate::types::error::Error::InvalidGrantIdException {
    error: aws_sdk_kms::types::error::InvalidGrantIdException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::TagException { message, .. } =>
  crate::types::error::Error::TagException {
    error: aws_sdk_kms::types::error::TagException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::MalformedPolicyDocumentException { message, .. } =>
  crate::types::error::Error::MalformedPolicyDocumentException {
    error: aws_sdk_kms::types::error::MalformedPolicyDocumentException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CustomKeyStoreInvalidStateException { message, .. } =>
  crate::types::error::Error::CustomKeyStoreInvalidStateException {
    error: aws_sdk_kms::types::error::CustomKeyStoreInvalidStateException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::CloudHsmClusterNotFoundException { message, .. } =>
  crate::types::error::Error::CloudHsmClusterNotFoundException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotFoundException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidCiphertextException { message, .. } =>
  crate::types::error::Error::InvalidCiphertextException {
    error: aws_sdk_kms::types::error::InvalidCiphertextException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque { obj } =>
            crate::types::error::Error::Opaque {
                obj: obj.clone()
            },
    }
}
