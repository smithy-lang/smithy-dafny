// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_dynamodb::operation::batch_execute_statement::BatchExecuteStatementOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchExecuteStatementOutput,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchExecuteStatementOutput::BatchExecuteStatementOutput {
        Responses: ::std::rc::Rc::new(match &value.responses {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::batch_statement_response::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 ConsumedCapacity: ::std::rc::Rc::new(match &value.consumed_capacity {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| crate::conversions::consumed_capacity::to_dafny(e)
,
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchExecuteStatementOutput,
    >
) -> aws_sdk_dynamodb::operation::batch_execute_statement::BatchExecuteStatementOutput {
    aws_sdk_dynamodb::operation::batch_execute_statement::BatchExecuteStatementOutput::builder()
          .set_responses(match (*dafny_value.Responses()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchStatementResponse>| crate::conversions::batch_statement_response::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
 .set_consumed_capacity(match (*dafny_value.ConsumedCapacity()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e: &::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ConsumedCapacity>| crate::conversions::consumed_capacity::from_dafny(e.clone())
,
            )
        ),
    _ => None
}
)
          .build()


}
