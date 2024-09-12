// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::simple_resource::SimpleResourceRef,
) -> ::dafny_runtime::Object<
  dyn crate::r#simple::positional::internaldafny::types::ISimpleResource,
> {
  let wrap = SimpleResourceWrapper {
      obj: value.clone(),
  };
  let inner = ::std::rc::Rc::new(::std::cell::UnsafeCell::new(wrap));
  ::dafny_runtime::Object (Some(inner) )
}

pub struct SimpleResourceWrapper {
  obj: crate::types::simple_resource::SimpleResourceRef,
}

impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any> for SimpleResourceWrapper {
  ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<
      dyn crate::r#simple::positional::internaldafny::types::ISimpleResource,
    >,
) -> crate::types::simple_resource::SimpleResourceRef {
    let wrap = ISimpleResourceDafnyWrapper {
        obj: dafny_value.clone(),
    };
    crate::types::simple_resource::SimpleResourceRef {
      inner: ::std::rc::Rc::new(::std::cell::RefCell::new(wrap))
    }
}

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct ISimpleResourceDafnyWrapper {
  pub(crate) obj: ::dafny_runtime::Object<
      dyn crate::r#simple::positional::internaldafny::types::ISimpleResource,
  >,
}


impl crate::simple::positional::internaldafny::types::ISimpleResource
  for SimpleResourceWrapper
{
  fn r#_GetName_k(
      &mut self,
      input: &::std::rc::Rc<
      crate::r#simple::positional::internaldafny::types::GetNameInput,
      >,
  ) -> ::std::rc::Rc<
      crate::r#_Wrappers_Compile::Result<
          ::std::rc::Rc<
          crate::r#simple::positional::internaldafny::types::GetNameOutput,
          >,
          ::std::rc::Rc<crate::r#simple::positional::internaldafny::types::Error>,
      >,
  >
  {
      let inner_input =
          crate::conversions::get_name::_get_name_input::from_dafny(
              input.clone(),
          );
      let inner_result = self.obj.inner.borrow_mut().get_name(inner_input);
      let result = match inner_result {
          Ok(x) => crate::r#_Wrappers_Compile::Result::Success {
              value: crate::conversions::get_name::_get_name_output::to_dafny(
                  x,
              ),
          },
          Err(x) => crate::r#_Wrappers_Compile::Result::Failure {
              error: crate::conversions::error::to_dafny(x),
          },
      };
      ::std::rc::Rc::new(result)
  }
}

impl crate::types::simple_resource::SimpleResource for ISimpleResourceDafnyWrapper {
  fn get_name(
      &mut self,
      input: crate::operation::get_name::GetNameInput,
  ) -> Result<
      crate::operation::get_name::GetNameOutput,
      crate::types::error::Error,
  > {
      let inner_input =
          crate::conversions::get_name::_get_name_input::to_dafny(input);
      let inner_result = ::dafny_runtime::md!(self.obj.clone()).GetName(&inner_input);
      if matches!(
          inner_result.as_ref(),
          crate::r#_Wrappers_Compile::Result::Success { .. }
      ) {
          Ok(
              crate::conversions::get_name::_get_name_output::from_dafny(
                  inner_result.value().clone(),
              ),
          )
      } else {
          Err(crate::conversions::error::from_dafny(
              inner_result.error().clone(),
          ))
      }
  }
}
