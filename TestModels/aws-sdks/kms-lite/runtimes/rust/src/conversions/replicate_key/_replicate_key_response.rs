// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::replicate_key::ReplicateKeyOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReplicateKeyResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::ReplicateKeyResponse::ReplicateKeyResponse {
        ReplicaKeyMetadata: ::std::rc::Rc::new(match &value.replica_key_metadata {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::key_metadata::to_dafny(&x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 ReplicaPolicy: crate::standard_library_conversions::ostring_to_dafny(&value.replica_policy),
 ReplicaTags: ::std::rc::Rc::new(match &value.replica_tags {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::tag::to_dafny(&e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
