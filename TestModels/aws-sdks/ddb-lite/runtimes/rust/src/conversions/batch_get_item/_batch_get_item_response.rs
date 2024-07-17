// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::batch_get_item::BatchGetItemOutput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemOutput,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemOutput::BatchGetItemOutput {
        Responses:
::std::rc::Rc::new(match &value.responses {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(v,
    |e| ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&e.clone(),
    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
    |v| crate::conversions::attribute_value::to_dafny(&v)
,
)
,
)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 UnprocessedKeys:
::std::rc::Rc::new(match &value.unprocessed_keys {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| crate::conversions::keys_and_attributes::to_dafny(&v)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ConsumedCapacity: ::std::rc::Rc::new(match &value.consumed_capacity {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::consumed_capacity::to_dafny(&e)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
