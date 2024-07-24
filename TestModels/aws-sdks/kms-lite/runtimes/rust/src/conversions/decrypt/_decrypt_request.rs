// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::decrypt::DecryptInput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest::DecryptRequest {
        CiphertextBlob: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_blob).Extract(),
 EncryptionContext:
::std::rc::Rc::new(match &value.encryption_context {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(v),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 GrantTokens: ::std::rc::Rc::new(match &value.grant_tokens {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(e),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id),
 EncryptionAlgorithm: ::std::rc::Rc::new(match &value.encryption_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 Recipient: ::std::rc::Rc::new(match &value.recipient {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::recipient_info::to_dafny(&x) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 DryRun: dafny_standard_library::conversion::obool_to_dafny(value.dry_run),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest,
    >,
    client: aws_sdk_kms::Client,
) -> aws_sdk_kms::operation::decrypt::builders::DecryptFluentBuilder {
    client.decrypt()
          .set_ciphertext_blob(Some(dafny_standard_library::conversion::blob_from_dafny(dafny_value.CiphertextBlob().clone())))
 .set_encryption_context(match (*dafny_value.EncryptionContext()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(v),
            )
        ),
    _ => None
}
)
 .set_grant_tokens(match (*dafny_value.GrantTokens()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_key_id(dafny_standard_library::conversion::ostring_from_dafny(dafny_value.KeyId().clone()))
 .set_encryption_algorithm(match &**dafny_value.EncryptionAlgorithm() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::encryption_algorithm_spec::from_dafny(value)
    ),
    _ => None,
}
)
 .set_recipient(match (*dafny_value.Recipient()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::recipient_info::from_dafny(value.clone())),
    _ => None,
}
)
 .set_dry_run(dafny_standard_library::conversion::obool_from_dafny(dafny_value.DryRun().clone()))
}
