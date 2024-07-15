// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_resources_config::SimpleResourcesConfig,
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
> {
    let inner = crate::implementation_from_dafny::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig::SimpleResourcesConfig {
        name : dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.name)
    };
    ::std::rc::Rc::new(inner)
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_simple_dresources_dinternaldafny_dtypes::SimpleResourcesConfig,
    >,
) -> crate::types::simple_resources_config::SimpleResourcesConfig {
    crate::types::simple_resources_config::SimpleResourcesConfig {
        name: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(
            &dafny_value.name(),
        ),
    }
}
