// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use std::sync::LazyLock;
use crate::conversions;

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct Client {
    pub inner: aws_sdk_dynamodb::Client
}

impl ::std::cmp::PartialEq for Client {
  fn eq(&self, other: &Self) -> bool {
    false
  }
}

impl ::std::convert::Into<Client> for aws_sdk_dynamodb::Client {
    fn into(self) -> Client {
        Client { inner: self }
    }
}

/// A runtime for executing operations on the asynchronous client in a blocking manner.
/// Necessary because Dafny only generates synchronous code.
static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_multi_thread()
          .enable_all()
          .build()
          .unwrap()
});

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
}

impl dafny_runtime::UpcastObject<dyn crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient);
}

impl crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient
  for Client {
  fn BatchExecuteStatement(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchExecuteStatementInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchExecuteStatementOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::batch_execute_statement::_batch_execute_statement_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.batch_execute_statement()
        .set_statements(inner_input.statements)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::batch_execute_statement::_batch_execute_statement_response::to_dafny,
    crate::conversions::batch_execute_statement::to_dafny_error)
}
 fn BatchGetItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchGetItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::batch_get_item::_batch_get_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.batch_get_item()
        .set_request_items(inner_input.request_items)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::batch_get_item::_batch_get_item_response::to_dafny,
    crate::conversions::batch_get_item::to_dafny_error)
}
 fn BatchWriteItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchWriteItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::BatchWriteItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::batch_write_item::_batch_write_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.batch_write_item()
        .set_request_items(inner_input.request_items)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_return_item_collection_metrics(inner_input.return_item_collection_metrics)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::batch_write_item::_batch_write_item_response::to_dafny,
    crate::conversions::batch_write_item::to_dafny_error)
}
 fn CreateTable(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::CreateTableInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::CreateTableOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::create_table::_create_table_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.create_table()
        .set_attribute_definitions(inner_input.attribute_definitions)
.set_table_name(inner_input.table_name)
.set_key_schema(inner_input.key_schema)
.set_local_secondary_indexes(inner_input.local_secondary_indexes)
.set_global_secondary_indexes(inner_input.global_secondary_indexes)
.set_billing_mode(inner_input.billing_mode)
.set_provisioned_throughput(inner_input.provisioned_throughput)
.set_stream_specification(inner_input.stream_specification)
.set_sse_specification(inner_input.sse_specification)
.set_tags(inner_input.tags)
.set_table_class(inner_input.table_class)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::create_table::_create_table_response::to_dafny,
    crate::conversions::create_table::to_dafny_error)
}
 fn DeleteItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DeleteItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DeleteItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::delete_item::_delete_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.delete_item()
        .set_table_name(inner_input.table_name)
.set_key(inner_input.key)
.set_expected(inner_input.expected)
.set_conditional_operator(inner_input.conditional_operator)
.set_return_values(inner_input.return_values)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_return_item_collection_metrics(inner_input.return_item_collection_metrics)
.set_condition_expression(inner_input.condition_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
.set_expression_attribute_values(inner_input.expression_attribute_values)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::delete_item::_delete_item_response::to_dafny,
    crate::conversions::delete_item::to_dafny_error)
}
 fn DescribeTable(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::DescribeTableOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::describe_table::_describe_table_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.describe_table()
        .set_table_name(inner_input.table_name)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::describe_table::_describe_table_response::to_dafny,
    crate::conversions::describe_table::to_dafny_error)
}
 fn ExecuteStatement(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteStatementInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteStatementOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::execute_statement::_execute_statement_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.execute_statement()
        .set_statement(inner_input.statement)
.set_parameters(inner_input.parameters)
.set_consistent_read(inner_input.consistent_read)
.set_next_token(inner_input.next_token)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_limit(inner_input.limit)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::execute_statement::_execute_statement_response::to_dafny,
    crate::conversions::execute_statement::to_dafny_error)
}
 fn ExecuteTransaction(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteTransactionInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ExecuteTransactionOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::execute_transaction::_execute_transaction_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.execute_transaction()
        .set_transact_statements(inner_input.transact_statements)
.set_client_request_token(inner_input.client_request_token)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::execute_transaction::_execute_transaction_response::to_dafny,
    crate::conversions::execute_transaction::to_dafny_error)
}
 fn GetItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::GetItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::GetItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::get_item::_get_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.get_item()
        .set_table_name(inner_input.table_name)
.set_key(inner_input.key)
.set_attributes_to_get(inner_input.attributes_to_get)
.set_consistent_read(inner_input.consistent_read)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_projection_expression(inner_input.projection_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::get_item::_get_item_response::to_dafny,
    crate::conversions::get_item::to_dafny_error)
}
 fn PutItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::PutItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::PutItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::put_item::_put_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.put_item()
        .set_table_name(inner_input.table_name)
.set_item(inner_input.item)
.set_expected(inner_input.expected)
.set_return_values(inner_input.return_values)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_return_item_collection_metrics(inner_input.return_item_collection_metrics)
.set_conditional_operator(inner_input.conditional_operator)
.set_condition_expression(inner_input.condition_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
.set_expression_attribute_values(inner_input.expression_attribute_values)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::put_item::_put_item_response::to_dafny,
    crate::conversions::put_item::to_dafny_error)
}
 fn Query(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::QueryInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::QueryOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::query::_query_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.query()
        .set_table_name(inner_input.table_name)
.set_index_name(inner_input.index_name)
.set_select(inner_input.select)
.set_attributes_to_get(inner_input.attributes_to_get)
.set_limit(inner_input.limit)
.set_consistent_read(inner_input.consistent_read)
.set_key_conditions(inner_input.key_conditions)
.set_query_filter(inner_input.query_filter)
.set_conditional_operator(inner_input.conditional_operator)
.set_scan_index_forward(inner_input.scan_index_forward)
.set_exclusive_start_key(inner_input.exclusive_start_key)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_projection_expression(inner_input.projection_expression)
.set_filter_expression(inner_input.filter_expression)
.set_key_condition_expression(inner_input.key_condition_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
.set_expression_attribute_values(inner_input.expression_attribute_values)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::query::_query_response::to_dafny,
    crate::conversions::query::to_dafny_error)
}
 fn Scan(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::ScanOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::scan::_scan_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.scan()
        .set_table_name(inner_input.table_name)
.set_index_name(inner_input.index_name)
.set_attributes_to_get(inner_input.attributes_to_get)
.set_limit(inner_input.limit)
.set_select(inner_input.select)
.set_scan_filter(inner_input.scan_filter)
.set_conditional_operator(inner_input.conditional_operator)
.set_exclusive_start_key(inner_input.exclusive_start_key)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_total_segments(inner_input.total_segments)
.set_segment(inner_input.segment)
.set_projection_expression(inner_input.projection_expression)
.set_filter_expression(inner_input.filter_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
.set_expression_attribute_values(inner_input.expression_attribute_values)
.set_consistent_read(inner_input.consistent_read)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::scan::_scan_response::to_dafny,
    crate::conversions::scan::to_dafny_error)
}
 fn TransactGetItems(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TransactGetItemsInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TransactGetItemsOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::transact_get_items::_transact_get_items_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.transact_get_items()
        .set_transact_items(inner_input.transact_items)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::transact_get_items::_transact_get_items_response::to_dafny,
    crate::conversions::transact_get_items::to_dafny_error)
}
 fn TransactWriteItems(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TransactWriteItemsInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::TransactWriteItemsOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::transact_write_items::_transact_write_items_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.transact_write_items()
        .set_transact_items(inner_input.transact_items)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_return_item_collection_metrics(inner_input.return_item_collection_metrics)
.set_client_request_token(inner_input.client_request_token)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::transact_write_items::_transact_write_items_response::to_dafny,
    crate::conversions::transact_write_items::to_dafny_error)
}
 fn UpdateItem(&self, input: &std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateItemInput>)
  -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::UpdateItemOutput>,
    std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
  >
> {
  let inner_input = crate::conversions::update_item::_update_item_request::from_dafny(input.clone());
  let native_result = tokio::task::block_in_place(|| {
    dafny_tokio_runtime.block_on(async {
      self.inner.update_item()
        .set_table_name(inner_input.table_name)
.set_key(inner_input.key)
.set_attribute_updates(inner_input.attribute_updates)
.set_expected(inner_input.expected)
.set_conditional_operator(inner_input.conditional_operator)
.set_return_values(inner_input.return_values)
.set_return_consumed_capacity(inner_input.return_consumed_capacity)
.set_return_item_collection_metrics(inner_input.return_item_collection_metrics)
.set_update_expression(inner_input.update_expression)
.set_condition_expression(inner_input.condition_expression)
.set_expression_attribute_names(inner_input.expression_attribute_names)
.set_expression_attribute_values(inner_input.expression_attribute_values)
        .send()
        .await
      })
    });
  crate::standard_library_conversions::result_to_dafny(&native_result,
    crate::conversions::update_item::_update_item_response::to_dafny,
    crate::conversions::update_item::to_dafny_error)
}
} #[allow(non_snake_case)]
impl crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::_default {
  pub fn DynamoDBClient() -> ::std::rc::Rc<
    crate::r#_Wrappers_Compile::Result<
      ::dafny_runtime::Object<dyn crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::IDynamoDBClient>,
      ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
      >
    > {
    let shared_config = dafny_tokio_runtime.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
    let inner = aws_sdk_dynamodb::Client::new(&shared_config);
    let client = Client { inner };
    let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
    std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}
