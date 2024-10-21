
pub fn to_dafny(
    value: $qualifiedRustServiceErrorType:L,
) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    ::std::rc::Rc::new(match value {
        $toDafnyArms:L
        $qualifiedRustServiceErrorType:L::CollectionOfErrors { list, message } =>
            crate::r#$dafnyTypesModuleName:L::Error::CollectionOfErrors {
                message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&message),
                list: ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&list, |e| to_dafny(e.clone()))
            },
        $qualifiedRustServiceErrorType:L::ValidationError(inner) => {
	    let error_str = format!("{:?}", inner); 
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: {
                    let rc = ::std::rc::Rc::new(inner) as ::std::rc::Rc<dyn ::std::any::Any>;
                    // safety: `rc` is new, ensuring it has refcount 1 and is uniquely owned.
                    // we should use `dafny_runtime_conversions::rc_struct_to_dafny_class` once it
                    // accepts unsized types (https://github.com/dafny-lang/dafny/pull/5769)
                    unsafe { ::dafny_runtime::Object::from_rc(rc) }
                },
		alt_text : {
		  ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&error_str)
		}
            }
	},
        $qualifiedRustServiceErrorType:L::Opaque { obj, alt_text } =>
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0),
		alt_text: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&alt_text)
            },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
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
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj, alt_text } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone(),
		alt_text: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&alt_text)
            },
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj, alt_text } =>
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
                        obj: obj.clone(),
			alt_text: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&alt_text)
                    }
                }
            },
    }
}
