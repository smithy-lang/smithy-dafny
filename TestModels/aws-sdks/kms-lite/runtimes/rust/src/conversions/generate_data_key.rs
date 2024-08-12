pub mod _generate_data_key_request;

pub mod _generate_data_key_response;

use aws_sdk_kms::error::SdkError;
use crate::r#software::amazon::cryptography::services::kms::internaldafny::types::*;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<Error> {
  match value {
    SdkError::ServiceError(service_error) => match service_error.err() {
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DependencyTimeoutException(e) =>
            crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DisabledException(e) =>
            crate::conversions::error::disabled_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DryRunOperationException(e) =>
            crate::conversions::error::dry_run_operation_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::InvalidGrantTokenException(e) =>
            crate::conversions::error::invalid_grant_token_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::InvalidKeyUsageException(e) =>
            crate::conversions::error::invalid_key_usage_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KeyUnavailableException(e) =>
            crate::conversions::error::key_unavailable_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KmsInvalidStateException(e) =>
            crate::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::NotFoundException(e) =>
            crate::conversions::error::not_found_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
    },
    _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
    }
  }
}
