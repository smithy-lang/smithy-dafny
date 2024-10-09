// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
/// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
    ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::Opaque {
            obj: error_obj,
        },
    )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: ::dafny_runtime::DafnyType, E: 'static>(value: E) ->
    ::std::rc::Rc<
        crate::_Wrappers_Compile::Result<
            T,
            ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error>
        >
    >
{
    ::std::rc::Rc::new(crate::_Wrappers_Compile::Result::Failure {
        error: to_opaque_error(value),
    })
}
pub fn to_dafny(
    value: crate::deps::simple_multiplemodels_dependencyproject::types::error::Error,
) -> ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error> {
    ::std::rc::Rc::new(match value {
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::DependencyProjectError { message } =>
    crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::DependencyProjectError {
        message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&message),
    },
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::CollectionOfErrors { list, message } =>
            crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::CollectionOfErrors {
                message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&message),
                list: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&list, |e| to_dafny(e.clone()))
            },
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::ValidationError(inner) =>
            crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::Opaque {
                obj: {
                    let rc = ::std::rc::Rc::new(inner) as ::std::rc::Rc<dyn ::std::any::Any>;
                    // safety: `rc` is new, ensuring it has refcount 1 and is uniquely owned.
                    // we should use `dafny_runtime_conversions::rc_struct_to_dafny_class` once it
                    // accepts unsized types (https://github.com/dafny-lang/dafny/pull/5769)
                    unsafe { ::dafny_runtime::Object::from_rc(rc) }
                },
            },
        crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::Opaque { obj } =>
            crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error,
    >,
) -> crate::deps::simple_multiplemodels_dependencyproject::types::error::Error {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::DependencyProjectError { message } =>
    crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::DependencyProjectError {
        message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&message),
    },
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::CollectionOfErrors { list, message } =>
            crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::CollectionOfErrors {
                message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&message),
                list: ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&list, |e| from_dafny(e.clone()))
            },
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::Opaque { obj } =>
            crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::Opaque {
                obj: obj.clone()
            },
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error::Opaque { obj } =>
            {
                use ::std::any::Any;
                if ::dafny_runtime::is_object!(obj, crate::deps::simple_multiplemodels_dependencyproject::types::error::ValidationError) {
                    let typed = ::dafny_runtime::cast_object!(obj.clone(), crate::deps::simple_multiplemodels_dependencyproject::types::error::ValidationError);
                    crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::ValidationError(
                        // safety: dafny_class_to_struct will increment ValidationError's Rc
                        unsafe {
                            ::dafny_runtime::dafny_runtime_conversions::object::dafny_class_to_struct(typed)
                        }
                    )
                } else {
                    crate::deps::simple_multiplemodels_dependencyproject::types::error::Error::Opaque {
                        obj: obj.clone()
                    }
                }
            },
    }
}
