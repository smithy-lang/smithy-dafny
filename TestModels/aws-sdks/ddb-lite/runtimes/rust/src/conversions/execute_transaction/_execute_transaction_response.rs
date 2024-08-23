// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::execute_transaction::ExecuteTransactionOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteTransactionOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteTransactionOutput::ExecuteTransactionOutput {
        Responses: ::std::rc::Rc::new(match &value.responses {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::item_response::to_dafny(&e)
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
