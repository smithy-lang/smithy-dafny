pub mod _encrypt_request;

pub mod _encrypt_response;

use aws_sdk_kms::error::SdkError;
use crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::*;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::encrypt::EncryptError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<Error> {
    match value {
        SdkError::ServiceError(service_error) => match service_error.err() {
            aws_sdk_kms::operation::encrypt::EncryptError::DependencyTimeoutException(e) => {
                crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone())
            }
            aws_sdk_kms::operation::encrypt::EncryptError::DisabledException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::DryRunOperationException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::InvalidGrantTokenException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::InvalidKeyUsageException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::KeyUnavailableException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::KmsInternalException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::KmsInvalidStateException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::NotFoundException(_) => todo!(),
            aws_sdk_kms::operation::encrypt::EncryptError::Unhandled(_) => todo!(),
            _ => todo!(),
        },
        _ => {
            panic!()
            // crate::conversions::error::to_opaque_error(value)
        }
    }
}
