// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::get_public_key::GetPublicKeyOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetPublicKeyResponse::GetPublicKeyResponse {
        KeyId: crate::standard_library_conversions::ostring_to_dafny(&value.key_id),
 PublicKey: crate::standard_library_conversions::oblob_to_dafny(&value.public_key),
 CustomerMasterKeySpec: ::std::rc::Rc::new(match &value.customer_master_key_spec {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::customer_master_key_spec::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 KeySpec: ::std::rc::Rc::new(match &value.key_spec {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::key_spec::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 KeyUsage: ::std::rc::Rc::new(match &value.key_usage {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::key_usage_type::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 EncryptionAlgorithms: ::std::rc::Rc::new(match &value.encryption_algorithms {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::encryption_algorithm_spec::to_dafny(e.clone()),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 SigningAlgorithms: ::std::rc::Rc::new(match &value.signing_algorithms {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::signing_algorithm_spec::to_dafny(e.clone()),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 KeyAgreementAlgorithms: ::std::rc::Rc::new(match &value.key_agreement_algorithms {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::key_agreement_algorithm_spec::to_dafny(e.clone()),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
