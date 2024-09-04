// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_aggregate_known_value_test::GetAggregateInput,
) -> ::std::rc::Rc<
    crate::r#simple::aggregate::internaldafny::types::GetAggregateInput,
>{
    ::std::rc::Rc::new(crate::r#simple::aggregate::internaldafny::types::GetAggregateInput::GetAggregateInput {
        simpleStringList: ::std::rc::Rc::new(match &value.simple_string_list {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&e),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 structureList: ::std::rc::Rc::new(match &value.structure_list {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::structure_list_element::to_dafny(e.clone())
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 simpleStringMap:
::std::rc::Rc::new(match &value.simple_string_map {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&v),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 simpleIntegerMap:
::std::rc::Rc::new(match &value.simple_integer_map {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| v.clone(),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 nestedStructure: ::std::rc::Rc::new(match &value.nested_structure {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::nested_structure::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::aggregate::internaldafny::types::GetAggregateInput,
    >,
) -> crate::operation::get_aggregate_known_value_test::GetAggregateInput {
    crate::operation::get_aggregate_known_value_test::GetAggregateInput::builder()
        .set_simple_string_list(match (*dafny_value.simpleStringList()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_structure_list(match (*dafny_value.structureList()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| crate::conversions::structure_list_element::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
 .set_simple_string_map(match (*dafny_value.simpleStringMap()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(v),
            )
        ),
    _ => None
}
)
 .set_simple_integer_map(match (*dafny_value.simpleIntegerMap()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| v .clone(),
            )
        ),
    _ => None
}
)
 .set_nested_structure(match (*dafny_value.nestedStructure()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::nested_structure::from_dafny(value.clone())),
    _ => None,
}
)
        .build()
        .unwrap()
}
