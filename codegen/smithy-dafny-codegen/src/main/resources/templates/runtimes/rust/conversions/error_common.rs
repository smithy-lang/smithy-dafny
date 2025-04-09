/// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error(value: String) ->
    ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>
{
    let error_msg = value.clone();
    let error_msg = ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&error_msg);
    let error_obj: ::dafny_runtime::Object<::dafny_runtime::DynAny> = ::dafny_runtime::Object(Some(
        ::dafny_runtime::Rc::new(::dafny_runtime::UnsafeCell::new(value)),
    ));
    ::dafny_runtime::Rc::new(
        crate::r#$dafnyTypesModuleName:L::Error::OpaqueWithText {
            obj: error_obj,
	    objMessage: error_msg
        },
    )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: ::dafny_runtime::DafnyType>(value: String) ->
    ::dafny_runtime::Rc<
        crate::_Wrappers_Compile::Result<
            T,
            ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>
        >
    >
{
    ::dafny_runtime::Rc::new(crate::_Wrappers_Compile::Result::Failure {
        error: to_opaque_error(value),
    })
}
