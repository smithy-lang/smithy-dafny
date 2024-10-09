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
  fn CancelKeyDeletion(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CancelKeyDeletionRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CancelKeyDeletionResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::cancel_key_deletion::_cancel_key_deletion_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.cancel_key_deletion()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::cancel_key_deletion::_cancel_key_deletion_response::to_dafny,
    crate::conversions::cancel_key_deletion::to_dafny_error)
}
 fn ConnectCustomKeyStore(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectCustomKeyStoreRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ConnectCustomKeyStoreResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::connect_custom_key_store::_connect_custom_key_store_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.connect_custom_key_store()
        .set_custom_key_store_id(inner_input.custom_key_store_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::connect_custom_key_store::_connect_custom_key_store_response::to_dafny,
    crate::conversions::connect_custom_key_store::to_dafny_error)
}
 fn CreateAlias(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateAliasRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::create_alias::_create_alias_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.create_alias()
        .set_alias_name(inner_input.alias_name)
.set_target_key_id(inner_input.target_key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::create_alias::to_dafny_error)
}
 fn CreateCustomKeyStore(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateCustomKeyStoreRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateCustomKeyStoreResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::create_custom_key_store::_create_custom_key_store_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.create_custom_key_store()
        .set_custom_key_store_name(inner_input.custom_key_store_name)
.set_cloud_hsm_cluster_id(inner_input.cloud_hsm_cluster_id)
.set_trust_anchor_certificate(inner_input.trust_anchor_certificate)
.set_key_store_password(inner_input.key_store_password)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::create_custom_key_store::_create_custom_key_store_response::to_dafny,
    crate::conversions::create_custom_key_store::to_dafny_error)
}
 fn CreateGrant(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateGrantRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateGrantResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::create_grant::_create_grant_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.create_grant()
        .set_key_id(inner_input.key_id)
.set_grantee_principal(inner_input.grantee_principal)
.set_retiring_principal(inner_input.retiring_principal)
.set_operations(inner_input.operations)
.set_constraints(inner_input.constraints)
.set_grant_tokens(inner_input.grant_tokens)
.set_name(inner_input.name)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::create_grant::_create_grant_response::to_dafny,
    crate::conversions::create_grant::to_dafny_error)
}
 fn CreateKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::create_key::_create_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.create_key()
        .set_policy(inner_input.policy)
.set_description(inner_input.description)
.set_key_usage(inner_input.key_usage)
.set_customer_master_key_spec(inner_input.customer_master_key_spec)
.set_key_spec(inner_input.key_spec)
.set_origin(inner_input.origin)
.set_custom_key_store_id(inner_input.custom_key_store_id)
.set_bypass_policy_lockout_safety_check(inner_input.bypass_policy_lockout_safety_check)
.set_tags(inner_input.tags)
.set_multi_region(inner_input.multi_region)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::create_key::_create_key_response::to_dafny,
    crate::conversions::create_key::to_dafny_error)
}
 fn Decrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptRequest>)
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
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::decrypt::_decrypt_response::to_dafny,
    crate::conversions::decrypt::to_dafny_error)
}
 fn DeleteAlias(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeleteAliasRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::delete_alias::_delete_alias_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.delete_alias()
        .set_alias_name(inner_input.alias_name)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::delete_alias::to_dafny_error)
}
 fn DeleteCustomKeyStore(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeleteCustomKeyStoreRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeleteCustomKeyStoreResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::delete_custom_key_store::_delete_custom_key_store_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.delete_custom_key_store()
        .set_custom_key_store_id(inner_input.custom_key_store_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::delete_custom_key_store::_delete_custom_key_store_response::to_dafny,
    crate::conversions::delete_custom_key_store::to_dafny_error)
}
 fn DeleteImportedKeyMaterial(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DeleteImportedKeyMaterialRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::delete_imported_key_material::_delete_imported_key_material_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.delete_imported_key_material()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::delete_imported_key_material::to_dafny_error)
}
 fn DescribeCustomKeyStores(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DescribeCustomKeyStoresRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DescribeCustomKeyStoresResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::describe_custom_key_stores::_describe_custom_key_stores_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.describe_custom_key_stores()
        .set_custom_key_store_id(inner_input.custom_key_store_id)
.set_custom_key_store_name(inner_input.custom_key_store_name)
.set_limit(inner_input.limit)
.set_marker(inner_input.marker)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::describe_custom_key_stores::_describe_custom_key_stores_response::to_dafny,
    crate::conversions::describe_custom_key_stores::to_dafny_error)
}
 fn DescribeKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DescribeKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DescribeKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::describe_key::_describe_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.describe_key()
        .set_key_id(inner_input.key_id)
.set_grant_tokens(inner_input.grant_tokens)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::describe_key::_describe_key_response::to_dafny,
    crate::conversions::describe_key::to_dafny_error)
}
 fn DisableKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DisableKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::disable_key::_disable_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.disable_key()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::disable_key::to_dafny_error)
}
 fn DisableKeyRotation(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DisableKeyRotationRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::disable_key_rotation::_disable_key_rotation_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.disable_key_rotation()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::disable_key_rotation::to_dafny_error)
}
 fn DisconnectCustomKeyStore(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DisconnectCustomKeyStoreRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DisconnectCustomKeyStoreResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::disconnect_custom_key_store::_disconnect_custom_key_store_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.disconnect_custom_key_store()
        .set_custom_key_store_id(inner_input.custom_key_store_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::disconnect_custom_key_store::_disconnect_custom_key_store_response::to_dafny,
    crate::conversions::disconnect_custom_key_store::to_dafny_error)
}
 fn EnableKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EnableKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::enable_key::_enable_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.enable_key()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::enable_key::to_dafny_error)
}
 fn EnableKeyRotation(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EnableKeyRotationRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::enable_key_rotation::_enable_key_rotation_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.enable_key_rotation()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::enable_key_rotation::to_dafny_error)
}
 fn Encrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::EncryptRequest>)
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
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::encrypt::_encrypt_response::to_dafny,
    crate::conversions::encrypt::to_dafny_error)
}
 fn GenerateDataKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyRequest>)
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
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key::_generate_data_key_response::to_dafny,
    crate::conversions::generate_data_key::to_dafny_error)
}
 fn GenerateDataKeyPair(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::generate_data_key_pair::_generate_data_key_pair_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.generate_data_key_pair()
        .set_encryption_context(inner_input.encryption_context)
.set_key_id(inner_input.key_id)
.set_key_pair_spec(inner_input.key_pair_spec)
.set_grant_tokens(inner_input.grant_tokens)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key_pair::_generate_data_key_pair_response::to_dafny,
    crate::conversions::generate_data_key_pair::to_dafny_error)
}
 fn GenerateDataKeyPairWithoutPlaintext(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairWithoutPlaintextRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyPairWithoutPlaintextResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::generate_data_key_pair_without_plaintext::_generate_data_key_pair_without_plaintext_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.generate_data_key_pair_without_plaintext()
        .set_encryption_context(inner_input.encryption_context)
.set_key_id(inner_input.key_id)
.set_key_pair_spec(inner_input.key_pair_spec)
.set_grant_tokens(inner_input.grant_tokens)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key_pair_without_plaintext::_generate_data_key_pair_without_plaintext_response::to_dafny,
    crate::conversions::generate_data_key_pair_without_plaintext::to_dafny_error)
}
 fn GenerateDataKeyWithoutPlaintext(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateDataKeyWithoutPlaintextRequest>)
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
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_data_key_without_plaintext::_generate_data_key_without_plaintext_response::to_dafny,
    crate::conversions::generate_data_key_without_plaintext::to_dafny_error)
}
 fn GenerateRandom(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateRandomRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateRandomResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::generate_random::_generate_random_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.generate_random()
        .set_number_of_bytes(inner_input.number_of_bytes)
.set_custom_key_store_id(inner_input.custom_key_store_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::generate_random::_generate_random_response::to_dafny,
    crate::conversions::generate_random::to_dafny_error)
}
 fn GetKeyPolicy(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyPolicyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyPolicyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::get_key_policy::_get_key_policy_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.get_key_policy()
        .set_key_id(inner_input.key_id)
.set_policy_name(inner_input.policy_name)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::get_key_policy::_get_key_policy_response::to_dafny,
    crate::conversions::get_key_policy::to_dafny_error)
}
 fn GetKeyRotationStatus(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyRotationStatusRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyRotationStatusResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::get_key_rotation_status::_get_key_rotation_status_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.get_key_rotation_status()
        .set_key_id(inner_input.key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::get_key_rotation_status::_get_key_rotation_status_response::to_dafny,
    crate::conversions::get_key_rotation_status::to_dafny_error)
}
 fn GetParametersForImport(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetParametersForImportRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetParametersForImportResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::get_parameters_for_import::_get_parameters_for_import_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.get_parameters_for_import()
        .set_key_id(inner_input.key_id)
.set_wrapping_algorithm(inner_input.wrapping_algorithm)
.set_wrapping_key_spec(inner_input.wrapping_key_spec)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::get_parameters_for_import::_get_parameters_for_import_response::to_dafny,
    crate::conversions::get_parameters_for_import::to_dafny_error)
}
 fn GetPublicKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyRequest>)
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
 fn ImportKeyMaterial(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ImportKeyMaterialRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ImportKeyMaterialResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::import_key_material::_import_key_material_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.import_key_material()
        .set_key_id(inner_input.key_id)
.set_import_token(inner_input.import_token)
.set_encrypted_key_material(inner_input.encrypted_key_material)
.set_valid_to(inner_input.valid_to)
.set_expiration_model(inner_input.expiration_model)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::import_key_material::_import_key_material_response::to_dafny,
    crate::conversions::import_key_material::to_dafny_error)
}
 fn ListAliases(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListAliasesRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListAliasesResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::list_aliases::_list_aliases_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.list_aliases()
        .set_key_id(inner_input.key_id)
.set_limit(inner_input.limit)
.set_marker(inner_input.marker)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::list_aliases::_list_aliases_response::to_dafny,
    crate::conversions::list_aliases::to_dafny_error)
}
 fn ListGrants(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListGrantsRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListGrantsResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::list_grants::_list_grants_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.list_grants()
        .set_limit(inner_input.limit)
.set_marker(inner_input.marker)
.set_key_id(inner_input.key_id)
.set_grant_id(inner_input.grant_id)
.set_grantee_principal(inner_input.grantee_principal)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::list_grants::_list_grants_response::to_dafny,
    crate::conversions::list_grants::to_dafny_error)
}
 fn ListKeyPolicies(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListKeyPoliciesRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListKeyPoliciesResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::list_key_policies::_list_key_policies_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.list_key_policies()
        .set_key_id(inner_input.key_id)
.set_limit(inner_input.limit)
.set_marker(inner_input.marker)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::list_key_policies::_list_key_policies_response::to_dafny,
    crate::conversions::list_key_policies::to_dafny_error)
}
 fn ListResourceTags(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListResourceTagsRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ListResourceTagsResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::list_resource_tags::_list_resource_tags_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.list_resource_tags()
        .set_key_id(inner_input.key_id)
.set_limit(inner_input.limit)
.set_marker(inner_input.marker)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::list_resource_tags::_list_resource_tags_response::to_dafny,
    crate::conversions::list_resource_tags::to_dafny_error)
}
 fn PutKeyPolicy(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::PutKeyPolicyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::put_key_policy::_put_key_policy_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.put_key_policy()
        .set_key_id(inner_input.key_id)
.set_policy_name(inner_input.policy_name)
.set_policy(inner_input.policy)
.set_bypass_policy_lockout_safety_check(inner_input.bypass_policy_lockout_safety_check)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::put_key_policy::to_dafny_error)
}
 fn ReEncrypt(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReEncryptRequest>)
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
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::re_encrypt::_re_encrypt_response::to_dafny,
    crate::conversions::re_encrypt::to_dafny_error)
}
 fn ReplicateKey(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReplicateKeyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReplicateKeyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::replicate_key::_replicate_key_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.replicate_key()
        .set_key_id(inner_input.key_id)
.set_replica_region(inner_input.replica_region)
.set_policy(inner_input.policy)
.set_bypass_policy_lockout_safety_check(inner_input.bypass_policy_lockout_safety_check)
.set_description(inner_input.description)
.set_tags(inner_input.tags)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::replicate_key::_replicate_key_response::to_dafny,
    crate::conversions::replicate_key::to_dafny_error)
}
 fn RetireGrant(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RetireGrantRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::retire_grant::_retire_grant_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.retire_grant()
        .set_grant_token(inner_input.grant_token)
.set_key_id(inner_input.key_id)
.set_grant_id(inner_input.grant_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::retire_grant::to_dafny_error)
}
 fn RevokeGrant(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::RevokeGrantRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::revoke_grant::_revoke_grant_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.revoke_grant()
        .set_key_id(inner_input.key_id)
.set_grant_id(inner_input.grant_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::revoke_grant::to_dafny_error)
}
 fn ScheduleKeyDeletion(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ScheduleKeyDeletionRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ScheduleKeyDeletionResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::schedule_key_deletion::_schedule_key_deletion_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.schedule_key_deletion()
        .set_key_id(inner_input.key_id)
.set_pending_window_in_days(inner_input.pending_window_in_days)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::schedule_key_deletion::_schedule_key_deletion_response::to_dafny,
    crate::conversions::schedule_key_deletion::to_dafny_error)
}
 fn Sign(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SignRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SignResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::sign::_sign_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.sign()
        .set_key_id(inner_input.key_id)
.set_message(inner_input.message)
.set_message_type(inner_input.message_type)
.set_grant_tokens(inner_input.grant_tokens)
.set_signing_algorithm(inner_input.signing_algorithm)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::sign::_sign_response::to_dafny,
    crate::conversions::sign::to_dafny_error)
}
 fn TagResource(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::TagResourceRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::tag_resource::_tag_resource_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.tag_resource()
        .set_key_id(inner_input.key_id)
.set_tags(inner_input.tags)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::tag_resource::to_dafny_error)
}
 fn UntagResource(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UntagResourceRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::untag_resource::_untag_resource_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.untag_resource()
        .set_key_id(inner_input.key_id)
.set_tag_keys(inner_input.tag_keys)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::untag_resource::to_dafny_error)
}
 fn UpdateAlias(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateAliasRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::update_alias::_update_alias_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.update_alias()
        .set_alias_name(inner_input.alias_name)
.set_target_key_id(inner_input.target_key_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::update_alias::to_dafny_error)
}
 fn UpdateCustomKeyStore(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateCustomKeyStoreRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateCustomKeyStoreResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::update_custom_key_store::_update_custom_key_store_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.update_custom_key_store()
        .set_custom_key_store_id(inner_input.custom_key_store_id)
.set_new_custom_key_store_name(inner_input.new_custom_key_store_name)
.set_key_store_password(inner_input.key_store_password)
.set_cloud_hsm_cluster_id(inner_input.cloud_hsm_cluster_id)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::update_custom_key_store::_update_custom_key_store_response::to_dafny,
    crate::conversions::update_custom_key_store::to_dafny_error)
}
 fn UpdateKeyDescription(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateKeyDescriptionRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    (),
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::update_key_description::_update_key_description_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.update_key_description()
        .set_key_id(inner_input.key_id)
.set_description(inner_input.description)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    |x| (),
    crate::conversions::update_key_description::to_dafny_error)
}
 fn UpdatePrimaryRegion(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdatePrimaryRegionRequest>)
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
 fn Verify(&mut self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::VerifyRequest>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::VerifyResponse>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::verify::_verify_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.verify()
        .set_key_id(inner_input.key_id)
.set_message(inner_input.message)
.set_message_type(inner_input.message_type)
.set_signature(inner_input.signature)
.set_signing_algorithm(inner_input.signing_algorithm)
.set_grant_tokens(inner_input.grant_tokens)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::verify::_verify_response::to_dafny,
    crate::conversions::verify::to_dafny_error)
}
} 
