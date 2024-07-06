// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::StructureListElement,
) -> ::std::rc::Rc<
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
> {
    ::std::rc::Rc::new(::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
  stringValue: dafny_standard_library::conversion::ostring_to_dafny(&value.string_value),
  integerValue: dafny_standard_library::conversion::oint_to_dafny(value.integer_value),
})
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::StructureListElement,
) -> ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement {
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
  stringValue: dafny_standard_library::conversion::ostring_to_dafny(&value.string_value),
  integerValue: dafny_standard_library::conversion::oint_to_dafny(value.integer_value),
}
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: Option<crate::types::StructureListElement>,
) -> ::std::rc::Rc<simple_aggregate_dafny::_Wrappers_Compile::Option<::std::rc::Rc<
  ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
>>>{
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
        ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
    >,
) -> crate::types::StructureListElement {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value : &::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
) -> crate::types::StructureListElement {
    match dafny_value {
    ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement::StructureListElement {
      stringValue,
      integerValue,
    } =>
    crate::types::StructureListElement {
      string_value: dafny_standard_library::conversion::ostring_from_dafny(stringValue.clone()),
      integer_value: dafny_standard_library::conversion::oint_from_dafny(integerValue.clone()),
    }
}
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<simple_aggregate_dafny::_Wrappers_Compile::Option<::std::rc::Rc<
        ::simple_aggregate_dafny::r#_simple_daggregate_dinternaldafny_dtypes::StructureListElement,
    >>>,
) -> Option<crate::types::StructureListElement> {
    match &*dafny_value {
        simple_aggregate_dafny::_Wrappers_Compile::Option::Some { value } => {
            Some(plain_from_dafny(value))
        }
        _ => None,
    }
}

// structure_list_element.rs
