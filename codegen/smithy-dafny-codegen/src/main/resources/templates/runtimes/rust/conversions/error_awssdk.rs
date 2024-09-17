
pub fn to_dafny(
    value: $qualifiedRustServiceErrorType:L,
) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
    match value {
        $toDafnyArms:L
        $qualifiedRustServiceErrorType:L::Opaque { obj } =>
            ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
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
        crate::r#$dafnyTypesModuleName:L::Error::Opaque { obj } =>
            $qualifiedRustServiceErrorType:L::Opaque {
                obj: obj.clone()
            },
    }
}