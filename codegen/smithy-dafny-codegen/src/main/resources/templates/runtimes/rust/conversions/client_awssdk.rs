// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

use std::any::Any;

pub fn to_dafny(
    value: &$rustClientType:L,
) ->
  ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$sdkId:LClient>
{
  let x: std::rc::Rc<$rustClientType:L> = std::rc::Rc::new(value.clone());
  let y = x as std::rc::Rc<dyn crate::r#$dafnyTypesModuleName:L::I$sdkId:LClient>;
  unsafe {
    ::dafny_runtime::dafny_runtime_conversions::object::rc_struct_to_dafny_class(y)
  }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<
      dyn crate::r#$dafnyTypesModuleName:L::I$sdkId:LClient
    >,
) -> $rustClientType:L {
  let as_boxed_any = dafny_runtime::cast_any_object!(dafny_value);
  if (dafny_runtime::is_object!(as_boxed_any, $rustClientType:L)) {
    let as_boxed_client = ::dafny_runtime::object::downcast::<$rustClientType:L>(as_boxed_any);
    unsafe {
      ::dafny_runtime::dafny_runtime_conversions::object::dafny_class_to_rc_struct(as_boxed_client).as_ref().clone()
    }
  } else {
    panic!("Unexpected implementation of Dafny client interface");
  }
}