pub mod _generate_data_key_request;

pub mod _generate_data_key_response;


use aws_sdk_kms::error::SdkError;
use crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::*;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: ::aws_smithy_runtime_api::client::result::SdkError<
      aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError,
      ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
  >,
) -> ::std::rc::Rc<Error> {
  match value {
    SdkError::ServiceError(service_error) => {
      match service_error.err() {  
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DependencyTimeoutException(e) => 
          crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DisabledException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::DryRunOperationException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::InvalidGrantTokenException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::InvalidKeyUsageException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KeyUnavailableException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KmsInternalException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::KmsInvalidStateException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::NotFoundException(e) => todo!(),
        aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::Unhandled(e) => todo!(),
        _ => todo!(),
      }
    },
    _ => {
      let as_dafny_error = DafnyError { inner: value };
      ::std::rc::Rc::new(Error::Opaque { obj: dafny_runtime::upcast_object()(dafny_runtime::object::new(as_dafny_error)) })
    }
  }
  
}

struct DafnyError {
  inner: ::aws_smithy_runtime_api::client::result::SdkError<
    aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError,
    ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
  >
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for DafnyError {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}
