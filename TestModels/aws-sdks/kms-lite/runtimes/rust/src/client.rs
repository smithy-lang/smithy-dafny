use crate::conversions;

struct Client {
  inner: aws_sdk_kms::Client,

  rt: tokio::runtime::Runtime
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
      let native_result = 
        self.rt.block_on(conversions::decrypt::_decrypt_request::from_dafny(input.clone(), self.inner.clone()).send());
      dafny_standard_library::conversion::result_to_dafny(native_result, 
        conversions::decrypt::_decrypt_response::to_dafny,
        conversions::decrypt::to_dafny_error)
    }
  
    fn Encrypt(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
      let native_result = 
        self.rt.block_on(conversions::encrypt::_encrypt_request::from_dafny(input.clone(), self.inner.clone()).send());
      dafny_standard_library::conversion::result_to_dafny(native_result,
        conversions::encrypt::_encrypt_response::to_dafny,
        conversions::encrypt::to_dafny_error)
    }
  
    fn GenerateDataKey(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
      let native_result = 
        self.rt.block_on(conversions::generate_data_key::_generate_data_key_request::from_dafny(input.clone(), self.inner.clone()).send());
      dafny_standard_library::conversion::result_to_dafny(native_result, 
        conversions::generate_data_key::_generate_data_key_response::to_dafny,
        conversions::generate_data_key::to_dafny_error)
    }
  
    fn GenerateDataKeyWithoutPlaintext(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
      let native_result = 
        self.rt.block_on(conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_request::from_dafny(input.clone(), self.inner.clone()).send());
      dafny_standard_library::conversion::result_to_dafny(native_result, 
        conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_response::to_dafny,
        conversions::generate_data_key_without_plaintext::to_dafny_error)
    }
  
    fn DeriveSharedSecret(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest>) -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretResponse>, std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>> {
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
      return conversions::error::to_opaque_error_result(rt_result.err());
    }
    let rt = rt_result.unwrap();

    let shared_config = rt.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
    let inner = aws_sdk_kms::Client::new(&shared_config);
    let client = Client { inner, rt };
    let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
    std::rc::Rc::new(crate::implementation_from_dafny::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}
