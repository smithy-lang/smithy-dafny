#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::$snakeCaseConfigName:L::$configName:L,
) -> ::std::rc::Rc<
    crate::r#$dafnyTypesModuleName:L::$configName:L,
> {
    ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::$configName:L::$configName:L {})
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#$dafnyTypesModuleName:L::$configName:L,
    >,
) -> crate::types::$snakeCaseConfigName:L::$configName:L {
    crate::types::$snakeCaseConfigName:L::$configName:L {}
}