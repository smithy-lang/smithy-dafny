// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use crate::conversions;

struct Client {
    inner: aws_sdk_kms::Client,

    rt: tokio::runtime::Runtime,
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
}

impl dafny_runtime::UpcastObject<dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient);
}

impl crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient
  for Client {
 fn Decrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::decrypt::_decrypt_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::decrypt::_decrypt_response::to_dafny,
    conversions::decrypt::to_dafny_error)
}
 fn DeriveSharedSecret(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::derive_shared_secret::_derive_shared_secret_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::derive_shared_secret::_derive_shared_secret_response::to_dafny,
    conversions::derive_shared_secret::to_dafny_error)
}
 fn Encrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::encrypt::_encrypt_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::encrypt::_encrypt_response::to_dafny,
    conversions::encrypt::to_dafny_error)
}
 fn GenerateDataKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::generate_data_key::_generate_data_key_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::generate_data_key::_generate_data_key_response::to_dafny,
    conversions::generate_data_key::to_dafny_error)
}
 fn GenerateDataKeyWithoutPlaintext(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_response::to_dafny,
    conversions::generate_data_key_without_plaintext::to_dafny_error)
}
 fn GetPublicKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::get_public_key::_get_public_key_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::get_public_key::_get_public_key_response::to_dafny,
    conversions::get_public_key::to_dafny_error)
}
 fn ReEncrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::re_encrypt::_re_encrypt_request::from_dafny(input.clone(), self.inner.clone()).send());
  crate::standard_library_conversions::result_to_dafny(&native_result,
    conversions::re_encrypt::_re_encrypt_response::to_dafny,
    conversions::re_encrypt::to_dafny_error)
} }

#[allow(non_snake_case)]
impl crate::r#software::amazon::cryptography::services::kms::internaldafny::_default {
  pub fn KMSClient() -> ::std::rc::Rc<
    crate::r#_Wrappers_Compile::Result<
      ::dafny_runtime::Object<dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>,
      ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
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
    std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}
