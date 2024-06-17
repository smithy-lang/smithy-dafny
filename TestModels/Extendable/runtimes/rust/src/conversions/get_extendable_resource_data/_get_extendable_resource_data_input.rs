// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_extendable_resource_data::GetExtendableResourceDataInput,
) -> ::std::rc::Rc<
    ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput,
>{
    ::std::rc::Rc::new(::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput::GetExtendableResourceDataInput {
        stringValue: dafny_standard_library::conversion::ostring_to_dafny(value.string_value()),
        booleanValue: dafny_standard_library::conversion::obool_to_dafny(value.boolean_value()),
        integerValue: dafny_standard_library::conversion::oint_to_dafny(value.integer_value()),
        longValue: dafny_standard_library::conversion::olong_to_dafny(value.long_value()),
        blobValue: dafny_standard_library::conversion::oblob_to_dafny(value.blob_value())
  })
}
// _get_extendable_resource_data_Input
#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput,
    >,
) -> crate::operation::get_extendable_resource_data::GetExtendableResourceDataInput {
    match &*dafny_value {
        ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::GetExtendableResourceDataInput::GetExtendableResourceDataInput {
            blobValue,
            booleanValue,
            integerValue,
            longValue,
            stringValue,
        } =>
        crate::operation::get_extendable_resource_data::GetExtendableResourceDataInput {
            string_value: dafny_standard_library::conversion::ostring_from_dafny(stringValue.clone()),
            boolean_value: dafny_standard_library::conversion::obool_from_dafny(booleanValue.clone()),
            integer_value: dafny_standard_library::conversion::oint_from_dafny(integerValue.clone()),
            long_value: dafny_standard_library::conversion::olong_from_dafny(longValue.clone()),
            blob_value: dafny_standard_library::conversion::oblob_from_dafny(blobValue.clone())
         }
    }
}
