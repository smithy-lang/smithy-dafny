// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::execute_statement::ExecuteStatementOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteStatementOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteStatementOutput::ExecuteStatementOutput {
        Items: ::std::rc::Rc::new(match &value.items {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&e.clone(),
    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
    |v| crate::conversions::attribute_value::to_dafny(&v)
,
)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 NextToken: crate::standard_library_conversions::ostring_to_dafny(&value.next_token),
 ConsumedCapacity: ::std::rc::Rc::new(match &value.consumed_capacity {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::consumed_capacity::to_dafny(&x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 LastEvaluatedKey:
::std::rc::Rc::new(match &value.last_evaluated_key {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| crate::conversions::attribute_value::to_dafny(&v)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
 
