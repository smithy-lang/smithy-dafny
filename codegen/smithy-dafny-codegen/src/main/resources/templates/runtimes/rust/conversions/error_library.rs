
pub fn to_dafny(
    value: $qualifiedRustServiceErrorType:L,
) -> ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    ::dafny_runtime::Rc::new(match value {
        $toDafnyArms:L
        $qualifiedRustServiceErrorType:L::CollectionOfErrors { list, message } =>
            crate::r#$dafnyTypesModuleName:L::Error::CollectionOfErrors {
                message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&message),
                list: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&list, |e| to_dafny(e.clone()))
            },
        $qualifiedRustServiceErrorType:L::ValidationError(inner) =>
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: {
                    let rc = ::dafny_runtime::Rc::new(inner) as ::dafny_runtime::Rc<::dafny_runtime::DynAny>;
                    // safety: `rc` is new, ensuring it has refcount 1 and is uniquely owned.
                    // we should use `dafny_runtime_conversions::rc_struct_to_dafny_class` once it
                    // accepts unsized types (https://github.com/dafny-lang/dafny/pull/5769)
                    unsafe { ::dafny_runtime::Object::from_rc(rc) }
                },
            },
            $qualifiedRustServiceErrorType:L::Opaque { obj } =>
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            },
            $qualifiedRustServiceErrorType:L::OpaqueWithText { obj, objMessage } =>
            crate::r#$dafnyTypesModuleName:L::Error::OpaqueWithText {
                obj: ::dafny_runtime::Object(obj.0),
                objMessage: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&objMessage),
            },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Rc<
        crate::r#$dafnyTypesModuleName:L::Error,
    >,
) -> $qualifiedRustServiceErrorType:L {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        $fromDafnyArms:L
        crate::r#$dafnyTypesModuleName:L::Error::CollectionOfErrors { list, message } =>
            $qualifiedRustServiceErrorType:L::CollectionOfErrors {
                message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&message),
                list: ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&list, |e| from_dafny(e.clone()))
            },
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone()
            },
            crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj } =>
            {
                use ::std::any::Any;
                if ::dafny_runtime::is_object!(obj, $rustErrorModuleName:L::ValidationError) {
                    let typed = ::dafny_runtime::cast_object!(obj.clone(), $rustErrorModuleName:L::ValidationError);
                    $qualifiedRustServiceErrorType:L::ValidationError(
                        // safety: dafny_class_to_struct will increment ValidationError's Rc
                        unsafe {
                            ::dafny_runtime::dafny_runtime_conversions::object::dafny_class_to_struct(typed)
                        }
                    )
                } else {
                    $qualifiedRustServiceErrorType:L::Opaque {
                        obj: obj.clone()
                    }
                }
            },
            crate::r#$dafnyTypesModuleName:L::Error::OpaqueWithText { obj, objMessage } =>
            {
                use ::std::any::Any;
                if ::dafny_runtime::is_object!(obj, $rustErrorModuleName:L::ValidationError) {
                    let typed = ::dafny_runtime::cast_object!(obj.clone(), $rustErrorModuleName:L::ValidationError);
                    $qualifiedRustServiceErrorType:L::ValidationError(
                        // safety: dafny_class_to_struct will increment ValidationError's Rc
                        unsafe {
                            ::dafny_runtime::dafny_runtime_conversions::object::dafny_class_to_struct(typed)
                        }
                    )
                } else {
                    $qualifiedRustServiceErrorType:L::OpaqueWithText {
                        obj: obj.clone(),
                        objMessage: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&objMessage),
                    }
                }
            },
    }
}