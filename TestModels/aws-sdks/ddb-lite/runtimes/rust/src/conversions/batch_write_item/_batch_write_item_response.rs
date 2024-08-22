// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::batch_write_item::BatchWriteItemOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchWriteItemOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchWriteItemOutput::BatchWriteItemOutput {
        UnprocessedItems:
::std::rc::Rc::new(match &value.unprocessed_items {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&v,
    |e| crate::conversions::write_request::to_dafny(&e)
,
)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 ItemCollectionMetrics:
::std::rc::Rc::new(match &value.item_collection_metrics {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&v,
    |e| crate::conversions::item_collection_metrics::to_dafny(&e)
,
)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 ConsumedCapacity: ::std::rc::Rc::new(match &value.consumed_capacity {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::consumed_capacity::to_dafny(&e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
