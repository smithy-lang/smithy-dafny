// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::batch_get_item::BatchGetItemInput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput::BatchGetItemInput {
        RequestItems: ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&value.request_items.clone(),
    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
    |v| crate::conversions::keys_and_attributes::to_dafny(&v)
,
)
,
 ReturnConsumedCapacity: ::std::rc::Rc::new(match &value.return_consumed_capacity {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::return_consumed_capacity::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput,
    >,
    client: aws_sdk_dynamodb::Client,
) -> aws_sdk_dynamodb::operation::batch_get_item::builders::BatchGetItemFluentBuilder {
    client.batch_get_item()
          .set_request_items(Some( ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(&dafny_value.RequestItems(),
    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
    |v| crate::conversions::keys_and_attributes::from_dafny(v.clone())
,
)
 ))
 .set_return_consumed_capacity(match &**dafny_value.ReturnConsumedCapacity() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::return_consumed_capacity::from_dafny(value)
    ),
    _ => None,
}
)
}
