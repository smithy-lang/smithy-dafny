use dafny_standard_library::implementation_from_dafny;

struct Client {
  inner: aws_sdk_kms::Client,
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

impl dafny_runtime::UpcastObject<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient);
}

impl crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient
  for Client {
    fn Decrypt(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn DeriveSharedSecret(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn Encrypt(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn GenerateDataKey(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn GenerateDataKeyWithoutPlaintext(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn GetPublicKey(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GetPublicKeyRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GetPublicKeyResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  
    fn ReEncrypt(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
        todo!()
    }
  }

#[allow(non_snake_case)]
impl crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::_default {
  pub fn KMSClient() -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
      ::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>,
      ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>
      >
    > {
    let rt_result = tokio::runtime::Builder::new_current_thread()
      .enable_all()
      .build();
    if rt_result.is_err() {
      return ::std::rc::Rc::new(to_opaque_error_result(rt_result.err().unwrap()));
    }
    let rt = rt_result.unwrap();

    let shared_config = rt.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
    let inner = aws_sdk_kms::Client::new(&shared_config);
    let client = Client { inner };
    let dafny_client = ::dafny_runtime::upcast_object::<Client, dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>()(::dafny_runtime::object::new(client));
    std::rc::Rc::new(crate::implementation_from_dafny::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}

fn to_opaque_error_result(error: std::io::Error) -> crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>,
::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>
> {
  let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> =
      ::dafny_runtime::Object(Some(::std::rc::Rc::new(
          ::std::cell::UnsafeCell::new(error),
      )));
    implementation_from_dafny::_Wrappers_Compile::Result::Failure {
        error: ::std::rc::Rc::new(
            crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error::Opaque {
                obj: error_obj,
            },
        ),
    }
}