pub mod dependency_timeout_exception;

pub mod disabled_exception;

pub mod dry_run_operation_exception;

pub mod incorrect_key_exception;

pub mod invalid_ciphertext_exception;

pub mod invalid_grant_token_exception;

pub mod invalid_key_usage_exception;

pub mod key_unavailable_exception;

pub mod kms_internal_exception;

pub mod kms_invalid_state_exception;

pub mod not_found_exception;

/// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
  ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque {
        obj: error_obj,
    },
  )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: dafny_runtime::DafnyType, E: 'static>(value: E) ->
  ::std::rc::Rc<
    crate::_Wrappers_Compile::Result<
      T,
      ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
    >
  >
{
    ::std::rc::Rc::new(
        crate::_Wrappers_Compile::Result::Failure {
            error: to_opaque_error(value),
        },
    )
}
