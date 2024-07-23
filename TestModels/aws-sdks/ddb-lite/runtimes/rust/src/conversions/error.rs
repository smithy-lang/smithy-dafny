// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod conditional_check_failed_exception;

 pub mod internal_server_error;

 pub mod invalid_endpoint_exception;

 pub mod item_collection_size_limit_exceeded_exception;

 pub mod provisioned_throughput_exceeded_exception;

 pub mod request_limit_exceeded;

 pub mod resource_not_found_exception;

 pub mod transaction_conflict_exception;
 /// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
  ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error::Opaque {
        obj: error_obj,
    },
  )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: dafny_runtime::DafnyType, E: 'static>(value: E) ->
  ::std::rc::Rc<
    dafny_standard_library::implementation_from_dafny::_Wrappers_Compile::Result<
      T,
      ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error>
    >
  >
{
    ::std::rc::Rc::new(
        dafny_standard_library::implementation_from_dafny::_Wrappers_Compile::Result::Failure {
            error: to_opaque_error(value),
        },
    )
}
