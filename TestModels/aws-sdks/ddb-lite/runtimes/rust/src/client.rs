// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
use crate::conversions;

struct Client {
    inner: aws_sdk_dynamodb::Client,

    rt: tokio::runtime::Runtime,
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
    ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
}

impl dafny_runtime::UpcastObject<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient> for Client {
  ::dafny_runtime::UpcastObjectFn!(dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient);
}

impl crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient
  for Client {
 fn BatchGetItem(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::BatchGetItemOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::batch_get_item::_batch_get_item_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::batch_get_item::_batch_get_item_response::to_dafny,
    conversions::batch_get_item::to_dafny_error)
}
 fn GetItem(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::GetItemOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::get_item::_get_item_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::get_item::_get_item_response::to_dafny,
    conversions::get_item::to_dafny_error)
}
 fn PutItem(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::PutItemOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::put_item::_put_item_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::put_item::_put_item_response::to_dafny,
    conversions::put_item::to_dafny_error)
}
 fn Query(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::QueryOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::query::_query_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::query::_query_response::to_dafny,
    conversions::query::to_dafny_error)
}
 fn Scan(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ScanInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::ScanOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::scan::_scan_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::scan::_scan_response::to_dafny,
    conversions::scan::to_dafny_error)
}
 fn UpdateItem(&mut self, input: &std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::UpdateItemInput>)
  -> std::rc::Rc<crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::UpdateItemOutput>,
    std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
  >
> {
  let native_result =
    self.rt.block_on(conversions::update_item::_update_item_request::from_dafny(input.clone(), self.inner.clone()).send());
  dafny_standard_library::conversion::result_to_dafny(&native_result,
    conversions::update_item::_update_item_response::to_dafny,
    conversions::update_item::to_dafny_error)
} }

#[allow(non_snake_case)]
impl crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny::_default {
  pub fn DynamoDBClient() -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_Wrappers_Compile::Result<
      ::dafny_runtime::Object<dyn crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::IDynamoDBClient>,
      ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
      >
    > {
    let rt_result = tokio::runtime::Builder::new_current_thread()
      .enable_all()
      .build();
    if rt_result.is_err() {
      return conversions::error::to_opaque_error_result(rt_result.err());
    }
    let rt = rt_result.unwrap();

    let shared_config = rt.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
    let inner = aws_sdk_dynamodb::Client::new(&shared_config);
    let client = Client { inner, rt };
    let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
    std::rc::Rc::new(crate::implementation_from_dafny::r#_Wrappers_Compile::Result::Success { value: dafny_client })
  }
}
