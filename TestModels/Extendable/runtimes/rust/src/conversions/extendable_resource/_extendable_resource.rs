// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
use crate::types::extendable_resource::ExtendableResource;

#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::extendable_resource::ExtendableResourceRef,
) ->
::dafny_runtime::Object<dyn simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>
{
    let wrap = ExtendableResourceWrapper { obj: value.clone() };
    let inner : ::std::rc::Rc<::std::cell::UnsafeCell<dyn ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>>
    = ::std::rc::Rc::new(::std::cell::UnsafeCell::new(wrap));

    ::dafny_runtime::Object(Some(inner))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Object<dyn simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource>,
) -> crate::types::extendable_resource::ExtendableResourceRef {
    let wrap = ExtendableResourceDafnyWrapper {
        obj: dafny_value.clone(),
    };
    ::std::rc::Rc::new(::std::cell::RefCell::new(wrap))
}

#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct ExtendableResourceWrapper {
    obj: crate::types::extendable_resource::ExtendableResourceRef,
}

impl ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource
    for ExtendableResourceWrapper
{
    fn r#_GetExtendableResourceData_k(
        &mut self,
        input: &::std::rc::Rc<
            ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput,
        >,
    ) -> ::std::rc::Rc<
        ::simple_extendable_dafny::r#_Wrappers_Compile::Result<
            ::std::rc::Rc<
                ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataOutput,
            >,
            ::std::rc::Rc<::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error>,
        >,
    >
    {
        let inner_input =
            crate::conversions::get_extendable_resource_data::_get_extendable_resource_data_input::from_dafny(
                input.clone(),
            );
        let inner_result = self.obj.borrow_mut().get_extendable_resource_data(inner_input);
        let result = match inner_result {
            Ok(x) => ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Success {
                value: crate::conversions::get_extendable_resource_data::_get_extendable_resource_data_output::to_dafny(
                    x,
                ),
            },
            Err(x) => ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Failure {
                error: crate::conversions::get_extendable_resource_data::to_dafny_error(x),
            },
        };
        ::std::rc::Rc::new(result)
    }
    fn _AlwaysMultipleErrors_k(&mut self, input: & std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>)
    ->  std::rc::Rc<simple_extendable_dafny::_Wrappers_Compile::Result< std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>,  std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>
    { todo!() }
    fn _AlwaysModeledError_k(&mut self, input: & std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>)
    ->  std::rc::Rc<simple_extendable_dafny::_Wrappers_Compile::Result< std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>,  std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>
    {
        let inner_input =
        crate::conversions::always_modeled_error::_always_modeled_error_input::from_dafny(
            input.clone(),
        );
    let inner_result = self.obj.borrow_mut().always_modeled_error(inner_input);
    let result = match inner_result {
        Ok(x) => ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Success {
            value: crate::conversions::always_modeled_error::_always_modeled_error_output::to_dafny(
                x,
            ),
        },
        Err(x) => ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Failure {
            error: crate::conversions::always_modeled_error::to_dafny_error(x),
        },
    };
    ::std::rc::Rc::new(result)

    }
    fn _AlwaysOpaqueError_k(&mut self, input: & std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsInput>)
    ->  std::rc::Rc<simple_extendable_dafny::_Wrappers_Compile::Result< std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceErrorsOutput>,  std::rc::Rc<simple_extendable_dafny::_simple_dextendable_dresources_dinternaldafny_dtypes::Error>>>
    { todo!() }
 }

#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct ExtendableResourceDafnyWrapper {
    pub(crate) obj: ::dafny_runtime::Object<
        dyn ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::IExtendableResource,
    >,
}

impl ExtendableResource for ExtendableResourceDafnyWrapper {
    fn get_extendable_resource_data(
        &mut self,
        input: crate::operation::get_extendable_resource_data::GetExtendableResourceDataInput,
    ) -> Result<
        crate::operation::get_extendable_resource_data::GetExtendableResourceDataOutput,
        crate::operation::get_extendable_resource_data::GetExtendableResourceDataError,
    > {
        let inner_input =
            crate::conversions::get_extendable_resource_data::_get_extendable_resource_data_input::to_dafny(input);
        let inner_result =
            ::dafny_runtime::md!(self.obj.clone()).GetExtendableResourceData(&inner_input);
        if matches!(
            inner_result.as_ref(),
            ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::get_extendable_resource_data::_get_extendable_resource_data_output::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(
                crate::conversions::get_extendable_resource_data::from_dafny_error(
                    inner_result.error().clone(),
                ),
            )
        }
    }

    fn always_modeled_error(
        &mut self,
        input: crate::operation::always_modeled_error::AlwaysModeledErrorInput,
    ) -> Result<
        crate::operation::always_modeled_error::AlwaysModeledErrorOutput,
        crate::operation::always_modeled_error::AlwaysModeledErrorError,
    > {
        let inner_input =
            crate::conversions::always_modeled_error::_always_modeled_error_input::to_dafny(input);
        let inner_result = ::dafny_runtime::md!(self.obj.clone()).AlwaysModeledError(&inner_input);
        if matches!(
            inner_result.as_ref(),
            ::simple_extendable_dafny::r#_Wrappers_Compile::Result::Success { .. }
        ) {
            Ok(
                crate::conversions::always_modeled_error::_always_modeled_error_output::from_dafny(
                    inner_result.value().clone(),
                ),
            )
        } else {
            Err(crate::conversions::always_modeled_error::from_dafny_error(
                inner_result.error().clone(),
            ))
        }
    }
}
