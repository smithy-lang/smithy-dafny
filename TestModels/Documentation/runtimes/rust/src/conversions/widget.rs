// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::types::widget::WidgetRef,
) -> ::dafny_runtime::Object<
  dyn crate::r#simple::documentation::internaldafny::types::IWidget,
> {
  let wrap = WidgetWrapper {
      obj: value.clone(),
  };
  let inner = ::std::rc::Rc::new(::std::cell::UnsafeCell::new(wrap));
  ::dafny_runtime::Object (Some(inner) )
}

pub struct WidgetWrapper {
  obj: crate::types::widget::WidgetRef,
}

impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any> for WidgetWrapper {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<
      dyn crate::r#simple::documentation::internaldafny::types::IWidget,
    >,
) -> crate::types::widget::WidgetRef {
    let wrap = IWidgetDafnyWrapper {
        obj: dafny_value.clone(),
    };
    crate::types::widget::WidgetRef {
      inner: ::std::rc::Rc::new(::std::cell::RefCell::new(wrap))
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct IWidgetDafnyWrapper {
  pub(crate) obj: ::dafny_runtime::Object<
      dyn crate::r#simple::documentation::internaldafny::types::IWidget,
  >,
}

impl crate::simple::documentation::internaldafny::types::IWidget
  for WidgetWrapper
{
  fn r#_SetWidgetName_k(
    &mut self,
    input: &::std::rc::Rc<crate::simple::documentation::internaldafny::types::SetWidgetNameInput>,
) -> ::std::rc::Rc<
    crate::r#_Wrappers_Compile::Result<
        (),
        ::std::rc::Rc<crate::r#simple::documentation::internaldafny::types::Error>,
    >,
>
{
    let inner_input = crate::conversions::set_widget_name::_set_widget_name_input::from_dafny(input.clone());
    let inner_result = self.obj.inner.borrow_mut().set_widget_name(inner_input);
    let result = match inner_result {
        Ok(x) => crate::r#_Wrappers_Compile::Result::Success {
            value: (),
        },
        Err(x) => crate::r#_Wrappers_Compile::Result::Failure {
            error: crate::conversions::error::to_dafny(x),
        },
    };
    ::std::rc::Rc::new(result)
}
}

impl crate::types::widget::Widget for IWidgetDafnyWrapper
{
  fn set_widget_name(
  &mut self,
  input: crate::operation::set_widget_name::SetWidgetNameInput,
) -> Result<
  (),
  crate::types::error::Error,
> {
  let inner_input = crate::conversions::set_widget_name::_set_widget_name_input::to_dafny(input);
  let inner_result = ::dafny_runtime::md!(self.obj.clone()).SetWidgetName(&inner_input);
  if matches!(
      inner_result.as_ref(),
      crate::r#_Wrappers_Compile::Result::Success { .. }
  ) {
      Ok(
          (),
      )
  } else {
      Err(crate::conversions::error::from_dafny(
          inner_result.error().clone(),
      ))
  }
}
}
