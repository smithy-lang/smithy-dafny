// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.

/// A different kind of thing you can get.
/// Also exercising explicit @documentation traits, and multi-line strings to boot.
pub trait Widget {
    fn set_widget_name(
    &self,
    input: crate::operation::set_widget_name::SetWidgetNameInput,
  ) -> Result<
    (),
    crate::types::error::Error,
  >;
}

#[derive(::std::clone::Clone)]
/// A reference to a Widget
pub struct WidgetRef {
  pub inner: ::std::rc::Rc<std::cell::RefCell<dyn Widget>>
}

impl ::std::cmp::PartialEq for WidgetRef {
    fn eq(&self, other: &WidgetRef) -> bool {
        ::std::rc::Rc::ptr_eq(&self.inner, &other.inner)
    }
}

impl ::std::fmt::Debug for WidgetRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<WidgetRef>")
    }
}

mod set_widget_name;
