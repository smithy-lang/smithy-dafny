pub mod _decrypt_request;

pub mod _decrypt_response;

use aws_sdk_kms::error::SdkError;
use crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::*;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::decrypt::DecryptError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<Error> {
    match value {
        SdkError::ServiceError(service_error) => match service_error.err() {
            aws_sdk_kms::operation::decrypt::DecryptError::DependencyTimeoutException(e) =>
                crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::DisabledException(e) =>
                crate::conversions::error::disabled_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::DryRunOperationException(e) =>
                crate::conversions::error::dry_run_operation_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::IncorrectKeyException(e) =>
                crate::conversions::error::incorrect_key_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidCiphertextException(e) =>
                crate::conversions::error::invalid_ciphertext_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidGrantTokenException(e) =>
                crate::conversions::error::invalid_grant_token_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidKeyUsageException(e) =>
                crate::conversions::error::invalid_key_usage_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::KeyUnavailableException(e) =>
                crate::conversions::error::key_unavailable_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::KmsInternalException(e) =>
                crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::KmsInvalidStateException(e) =>
                crate::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
            aws_sdk_kms::operation::decrypt::DecryptError::NotFoundException(e) =>
                crate::conversions::error::not_found_exception::to_dafny(e.clone()),
            e => crate::conversions::error::to_opaque_error(e.to_string()),
        },
        _ => {
            crate::conversions::error::to_opaque_error(value.to_string())
        }
    }
}
