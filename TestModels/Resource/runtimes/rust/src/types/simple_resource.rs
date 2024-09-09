// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

pub trait SimpleResource {
    fn get_resource_data(
    &mut self,
    input: crate::operation::get_resource_data::GetResourceDataInput,
  ) -> Result<
    crate::operation::get_resource_data::GetResourceDataOutput,
    crate::operation::get_resource_data::GetResourceDataError,
  >;
}

#[derive(::std::clone::Clone)]
pub struct SimpleResourceRef {
  pub inner: ::std::rc::Rc<std::cell::RefCell<dyn SimpleResource>>
}

impl ::std::cmp::PartialEq for SimpleResourceRef {
    fn eq(&self, other: &SimpleResourceRef) -> bool {
        ::std::rc::Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl ::std::fmt::Debug for SimpleResourceRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<SimpleResourceRef>")
    }
}

mod get_resource_data;
