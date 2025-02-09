
pub fn to_dafny(
    value: $qualifiedRustServiceErrorType:L,
) -> ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    match value {
        $toDafnyArms:L
        $qualifiedRustServiceErrorType:L::Opaque { obj } =>
            ::dafny_runtime::Rc::new(crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            }),
        $qualifiedRustServiceErrorType:L::OpaqueWithText { obj, objMessage } =>
            ::dafny_runtime::Rc::new(crate::r#$dafnyTypesModuleName:L::Error::OpaqueWithText {
                obj: ::dafny_runtime::Object(obj.0),
                objMessage: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&objMessage),
            }),
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Rc<
        crate::r#$dafnyTypesModuleName:L::Error,
    >,
) -> $qualifiedRustServiceErrorType:L {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        $fromDafnyArms:L
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone()
            },
        crate::r#$dafnyTypesModuleName:L::Error::OpaqueWithText { obj, objMessage } =>
            $qualifiedRustServiceErrorType:L::OpaqueWithText {
                obj: obj.clone(),
                objMessage: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&objMessage),
            },
    }
}