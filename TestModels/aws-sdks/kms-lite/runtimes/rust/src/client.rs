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
  async fn KMSClient() -> ::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient> {
    let shared_config = aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()).await;
    let inner = aws_sdk_kms::Client::new(&shared_config);
    ::dafny_runtime::upcast_object::<Client, dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>()(::dafny_runtime::object::new(inner))
  }
}