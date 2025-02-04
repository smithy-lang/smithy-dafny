#[allow(dead_code)]
pub fn to_dafny(
    value: &$qualifiedRustUnionName:L,
) -> ::dafny_runtime::Rc<
    crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L,
> {
    ::dafny_runtime::Rc::new(match value {
        $toDafnyVariants:L
        _ => panic!("Unknown union variant: {:?}", value),
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Rc<
        crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L,
    >,
) -> $qualifiedRustUnionName:L {
    match &::dafny_runtime::Rc::unwrap_or_clone(dafny_value) {
        $fromDafnyVariants:L
    }
}