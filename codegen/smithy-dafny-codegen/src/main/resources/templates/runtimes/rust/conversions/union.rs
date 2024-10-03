#[allow(dead_code)]
pub fn to_dafny(
    value: &$qualifiedRustUnionName:L,
) -> ::std::rc::Rc<
    crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L,
> {
    ::std::rc::Rc::new(match value {
        $toDafnyVariants:L
        _ => panic!("Unknown union variant: {:?}", value),
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L,
    >,
) -> $qualifiedRustUnionName:L {
    match &::std::rc::Rc::unwrap_or_clone(dafny_value) {
        $fromDafnyVariants:L
    }
}