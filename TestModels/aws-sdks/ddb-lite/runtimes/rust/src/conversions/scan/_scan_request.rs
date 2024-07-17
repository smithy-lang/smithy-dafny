// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::scan::ScanInput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ScanInput,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ScanInput::ScanInput {
        TableName: dafny_standard_library::conversion::ostring_to_dafny(&value.table_name) .Extract(),
 IndexName: dafny_standard_library::conversion::ostring_to_dafny(&value.index_name),
 AttributesToGet: todo!(),
 Limit: todo!(),
 Select: ::std::rc::Rc::new(match &value.select {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::select::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 ScanFilter:
::std::rc::Rc::new(match &value.scan_filter {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| crate::conversions::condition::to_dafny(&v)
,
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ConditionalOperator: ::std::rc::Rc::new(match &value.conditional_operator {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::conditional_operator::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 ExclusiveStartKey:
::std::rc::Rc::new(match &value.exclusive_start_key {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| todo!(),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ReturnConsumedCapacity: ::std::rc::Rc::new(match &value.return_consumed_capacity {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::return_consumed_capacity::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 TotalSegments: todo!(),
 Segment: todo!(),
 ProjectionExpression: dafny_standard_library::conversion::ostring_to_dafny(&value.projection_expression),
 FilterExpression: dafny_standard_library::conversion::ostring_to_dafny(&value.filter_expression),
 ExpressionAttributeNames:
::std::rc::Rc::new(match &value.expression_attribute_names {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(v),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ExpressionAttributeValues:
::std::rc::Rc::new(match &value.expression_attribute_values {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
            |v| todo!(),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 ConsistentRead: dafny_standard_library::conversion::obool_to_dafny(&value.consistent_read),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ScanInput,
    >,
    client: aws_sdk_dynamodb::Client,
) -> aws_sdk_dynamodb::operation::scan::builders::ScanFluentBuilder {
    client.scan()
          .set_table_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.TableName()) ))
 .set_index_name(dafny_standard_library::conversion::ostring_from_dafny(dafny_value.IndexName().clone()))
 .set_attributes_to_get(todo!())
 .set_limit(todo!())
 .set_select(match &**dafny_value.Select() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::select::from_dafny(value)
    ),
    _ => None,
}
)
 .set_scan_filter(match (*dafny_value.ScanFilter()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| crate::conversions::condition::from_dafny(v.clone())
,
            )
        ),
    _ => None
}
)
 .set_conditional_operator(match &**dafny_value.ConditionalOperator() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::conditional_operator::from_dafny(value)
    ),
    _ => None,
}
)
 .set_exclusive_start_key(match (*dafny_value.ExclusiveStartKey()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| todo!(),
            )
        ),
    _ => None
}
)
 .set_return_consumed_capacity(match &**dafny_value.ReturnConsumedCapacity() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::return_consumed_capacity::from_dafny(value)
    ),
    _ => None,
}
)
 .set_total_segments(todo!())
 .set_segment(todo!())
 .set_projection_expression(dafny_standard_library::conversion::ostring_from_dafny(dafny_value.ProjectionExpression().clone()))
 .set_filter_expression(dafny_standard_library::conversion::ostring_from_dafny(dafny_value.FilterExpression().clone()))
 .set_expression_attribute_names(match (*dafny_value.ExpressionAttributeNames()).as_ref() {
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
 .set_expression_attribute_values(match (*dafny_value.ExpressionAttributeValues()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| todo!(),
            )
        ),
    _ => None
}
)
 .set_consistent_read(dafny_standard_library::conversion::obool_from_dafny(dafny_value.ConsistentRead().clone()))
}
