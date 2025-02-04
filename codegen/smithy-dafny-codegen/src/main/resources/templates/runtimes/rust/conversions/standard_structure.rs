#[allow(dead_code)]
pub fn to_dafny(
    value: &$qualifiedRustStructureType:L,
) -> ::dafny_runtime::Rc<
    crate::r#$dafnyTypesModuleName:L::$structureName:L,
> {
    ::dafny_runtime::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: $qualifiedRustStructureType:L,
) -> crate::r#$dafnyTypesModuleName:L::$structureName:L {
    crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {
        $variants:L
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<$qualifiedRustStructureType:L>,
) -> ::dafny_runtime::Rc<crate::_Wrappers_Compile::Option<::dafny_runtime::Rc<
  crate::r#$dafnyTypesModuleName:L::$structureName:L,
>>>{
    ::dafny_runtime::Rc::new(match value {
        ::std::option::Option::None => crate::_Wrappers_Compile::Option::None {},
        ::std::option::Option::Some(x) => crate::_Wrappers_Compile::Option::Some {
            value: ::dafny_runtime::Rc::new(to_dafny_plain(x)),
        },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::dafny_runtime::Rc<
        crate::r#$dafnyTypesModuleName:L::$structureName:L,
    >,
) -> $qualifiedRustStructureType:L {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#$dafnyTypesModuleName:L::$structureName:L,
) -> $qualifiedRustStructureType:L {
    match dafny_value {
        crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {..} =>
            $qualifiedRustStructureType:L::builder()
                $fluentMemberSetters:L
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::dafny_runtime::Rc<crate::_Wrappers_Compile::Option<::dafny_runtime::Rc<
        crate::r#$dafnyTypesModuleName:L::$structureName:L,
    >>>,
) -> ::std::option::Option<$qualifiedRustStructureType:L> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}