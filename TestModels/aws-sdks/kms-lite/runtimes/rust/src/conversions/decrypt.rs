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
            aws_sdk_kms::operation::decrypt::DecryptError::DependencyTimeoutException(e) => {
                crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone())
            }
            aws_sdk_kms::operation::decrypt::DecryptError::DisabledException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::DryRunOperationException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::IncorrectKeyException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidCiphertextException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidGrantTokenException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::InvalidKeyUsageException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::KeyUnavailableException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::KmsInternalException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::KmsInvalidStateException(_) => todo!(),
            aws_sdk_kms::operation::decrypt::DecryptError::NotFoundException(_) => todo!(),
            e => panic!(),
        },
        _ => {
            panic!()
            // crate::conversions::error::to_opaque_error(value)
        }
    }
}
