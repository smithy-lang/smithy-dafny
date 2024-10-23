// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use std::sync::LazyLock;
use crate::conversions;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub inner: aws_sdk_kms::Client
}

impl ::std::cmp::PartialEq for Client {
  fn eq(&self, other: &Self) -> bool {
    false
  }
}

impl ::std::convert::Into<Client> for aws_sdk_kms::Client {
    fn into(self) -> Client {
        Client { inner: self }
    }
}

/// A runtime for executing operations on the asynchronous client in a blocking manner.
/// Necessary because Dafny only generates synchronous code.
static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
          .enable_all()
          .build()
          .unwrap()
});

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
}

impl dafny_runtime::UpcastObject<dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient);
}

impl crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient
  for Client {
  fn Decrypt(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::decrypt::_decrypt_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.decrypt()
        .set_ciphertext_blob(inner_input.ciphertext_blob)
.set_encryption_context(inner_input.encryption_context)
.set_grant_tokens(inner_input.grant_tokens)
.set_key_id(inner_input.key_id)
.set_encryption_algorithm(inner_input.encryption_algorithm)
.set_recipient(inner_input.recipient)
.set_dry_run(inner_input.dry_run)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::decrypt::_decrypt_response::to_dafny,
    crate::conversions::decrypt::to_dafny_error)
}
 fn DeriveSharedSecret(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeriveSharedSecretResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::derive_shared_secret::_derive_shared_secret_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.derive_shared_secret()
        .set_key_id(inner_input.key_id)
.set_key_agreement_algorithm(inner_input.key_agreement_algorithm)
.set_public_key(inner_input.public_key)
.set_grant_tokens(inner_input.grant_tokens)
.set_dry_run(inner_input.dry_run)
.set_recipient(inner_input.recipient)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::derive_shared_secret::_derive_shared_secret_response::to_dafny,
    crate::conversions::derive_shared_secret::to_dafny_error)
}
 fn Encrypt(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EncryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::encrypt::_encrypt_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.encrypt()
        .set_key_id(inner_input.key_id)
.set_plaintext(inner_input.plaintext)
.set_encryption_context(inner_input.encryption_context)
.set_grant_tokens(inner_input.grant_tokens)
.set_encryption_algorithm(inner_input.encryption_algorithm)
.set_dry_run(inner_input.dry_run)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::encrypt::_encrypt_response::to_dafny,
    crate::conversions::encrypt::to_dafny_error)
}
 fn GenerateDataKey(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::generate_data_key::_generate_data_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.generate_data_key()
        .set_key_id(inner_input.key_id)
.set_encryption_context(inner_input.encryption_context)
.set_number_of_bytes(inner_input.number_of_bytes)
.set_key_spec(inner_input.key_spec)
.set_grant_tokens(inner_input.grant_tokens)
.set_recipient(inner_input.recipient)
.set_dry_run(inner_input.dry_run)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key::_generate_data_key_response::to_dafny,
    crate::conversions::generate_data_key::to_dafny_error)
}
 fn GenerateDataKeyWithoutPlaintext(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.generate_data_key_without_plaintext()
        .set_key_id(inner_input.key_id)
.set_encryption_context(inner_input.encryption_context)
.set_key_spec(inner_input.key_spec)
.set_number_of_bytes(inner_input.number_of_bytes)
.set_grant_tokens(inner_input.grant_tokens)
.set_dry_run(inner_input.dry_run)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_response::to_dafny,
    crate::conversions::generate_data_key_without_plaintext::to_dafny_error)
}
 fn GetPublicKey(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::get_public_key::_get_public_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.get_public_key()
        .set_key_id(inner_input.key_id)
.set_grant_tokens(inner_input.grant_tokens)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::get_public_key::_get_public_key_response::to_dafny,
    crate::conversions::get_public_key::to_dafny_error)
}
 fn ReEncrypt(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::re_encrypt::_re_encrypt_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.re_encrypt()
        .set_ciphertext_blob(inner_input.ciphertext_blob)
.set_source_encryption_context(inner_input.source_encryption_context)
.set_source_key_id(inner_input.source_key_id)
.set_destination_key_id(inner_input.destination_key_id)
.set_destination_encryption_context(inner_input.destination_encryption_context)
.set_source_encryption_algorithm(inner_input.source_encryption_algorithm)
.set_destination_encryption_algorithm(inner_input.destination_encryption_algorithm)
.set_grant_tokens(inner_input.grant_tokens)
.set_dry_run(inner_input.dry_run)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::re_encrypt::_re_encrypt_response::to_dafny,
    crate::conversions::re_encrypt::to_dafny_error)
}
 fn UpdatePrimaryRegion(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdatePrimaryRegionRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::update_primary_region::_update_primary_region_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.update_primary_region()
        .set_key_id(inner_input.key_id)
.set_primary_region(inner_input.primary_region)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::update_primary_region::to_dafny_error)
}
} #[allow(non_snake_case)]
impl crate::r#software::amazon::cryptography::services::kms::internaldafny::_default {
  pub fn KMSClient() -> ::std::rc::Rc<
    crate::r#_Wrappers_Compile::Result<
      ::dafny_runtime::Object<dyn crate::r#software::amazon::cryptography::services::kms::internaldafny::types::IKMSClient>,
      ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
      >
    > {
    let shared_config = dafny_tokio_runtime.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
    let inner = aws_sdk_kms::Client::new(&shared_config);
    let client = Client { inner };
    let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
    std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}
