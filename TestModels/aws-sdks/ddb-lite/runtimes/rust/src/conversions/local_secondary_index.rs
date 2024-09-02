// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::types::LocalSecondaryIndex,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::LocalSecondaryIndex>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::LocalSecondaryIndex::LocalSecondaryIndex {
        IndexName: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.index_name),
 KeySchema: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&value.key_schema,
    |e| crate::conversions::key_schema_element::to_dafny(&e)
,
)
,
 Projection: crate::conversions::projection::to_dafny(&value.projection.clone().unwrap())
,
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::LocalSecondaryIndex,
    >,
) -> aws_sdk_dynamodb::types::LocalSecondaryIndex {
    aws_sdk_dynamodb::types::LocalSecondaryIndex::builder()
          .set_index_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.IndexName()) ))
 .set_key_schema(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(dafny_value.KeySchema(),
    |e| crate::conversions::key_schema_element::from_dafny(e.clone())
,
)
 ))
 .set_projection(Some( crate::conversions::projection::from_dafny(dafny_value.Projection().clone())
 ))
          .build()
          .unwrap()
}
