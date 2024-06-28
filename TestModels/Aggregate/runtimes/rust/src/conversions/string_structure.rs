// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::StringStructure,
) -> ::std::rc::Rc<
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
> {
    ::std::rc::Rc::new(::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
  value: dafny_standard_library::conversion::ostring_to_dafny(&value.value),
})
}

pub fn to_dafny_plain(
    value: crate::types::StringStructure,
) -> ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure {
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
  value: dafny_standard_library::conversion::ostring_to_dafny(&value.value),
}
}

pub fn option_to_dafny(
    value: Option<crate::types::StringStructure>,
) -> ::std::rc::Rc<
    simple_aggregate_dafny::_Wrappers_Compile::Option<
        ::std::rc::Rc<
            ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
        >,
    >,
> {
    let inner = match value {
        None => simple_aggregate_dafny::_Wrappers_Compile::Option::None {},
        Some(x) => simple_aggregate_dafny::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(to_dafny_plain(x)),
        },
    };
    ::std::rc::Rc::new(inner)
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
    >,
) -> crate::types::StringStructure {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value : &::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
) -> crate::types::StringStructure {
    match dafny_value {
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure::StringStructure {
      value,
    } =>
    crate::types::StringStructure {
      value: dafny_standard_library::conversion::ostring_from_dafny(value.clone()),
    }
}
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<simple_aggregate_dafny::_Wrappers_Compile::Option<::std::rc::Rc<
        ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StringStructure,
    >>>,
) -> Option<crate::types::StringStructure> {
    match &*dafny_value {
        simple_aggregate_dafny::_Wrappers_Compile::Option::Some { value } => {
            Some(plain_from_dafny(value))
        }
        _ => None,
    }
}