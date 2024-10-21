
pub fn to_dafny(
    value: $qualifiedRustServiceErrorType:L,
) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    match value {
        $toDafnyArms:L
        $qualifiedRustServiceErrorType:L::Opaque { obj, alt_text } =>
            ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0),
		alt_text: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&alt_text)
            }),
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#$dafnyTypesModuleName:L::Error,
    >,
) -> $qualifiedRustServiceErrorType:L {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        $fromDafnyArms:L
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj, alt_text } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone(),
		alt_text: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&alt_text)
            },
    }
}
