pub mod _generate_data_key_without_plaintext_request;

pub mod _generate_data_key_without_plaintext_response;

use aws_sdk_kms::error::SdkError;
use crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::*;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
      aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError,
      ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
  >,
) -> ::std::rc::Rc<Error> {
    match value {
    SdkError::ServiceError(service_error) => {
      match service_error.err() {  
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::DependencyTimeoutException(e) => 
          crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::DisabledException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::DryRunOperationException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::InvalidGrantTokenException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::InvalidKeyUsageException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::KeyUnavailableException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::KmsInternalException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::KmsInvalidStateException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key_without_plaintext::GenerateDataKeyWithoutPlaintextError::NotFoundException(e) => todo!(),
        e => panic!(),
      }
    },
    _ => {
      // TODO: SdkError isn't clonable, we need to implement a clone function for it ourselves
      // crate::conversions::error::to_opaque_error(value)
      panic!()
    }
  }
}
