// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::query::QueryOutput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput::QueryOutput {
        Items: ::std::rc::Rc::new(match &value.items {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&e.clone(),
    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
    |v| crate::conversions::attribute_value::to_dafny(&v)
,
)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 Count: dafny_standard_library::conversion::oint_to_dafny(Some(value.count)),
 ScannedCount: dafny_standard_library::conversion::oint_to_dafny(Some(value.scanned_count)),
 LastEvaluatedKey:
::std::rc::Rc::new(match &value.last_evaluated_key {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| crate::conversions::attribute_value::to_dafny(&v)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ConsumedCapacity: ::std::rc::Rc::new(match &value.consumed_capacity {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::consumed_capacity::to_dafny(&x) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    })
}
