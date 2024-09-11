
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
        $qualifiedRustServiceErrorType:L::Opaque { obj } =>
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
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
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone()
            },
    }
}