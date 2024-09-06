// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
use crate::types::simple_resource::SimpleResource;
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_resources::GetResourcesOutput,
) -> ::std::rc::Rc<
    crate::r#simple::resources::internaldafny::types::GetResourcesOutput,
> {
    ::std::rc::Rc::new(crate::r#simple::resources::internaldafny::types::GetResourcesOutput::GetResourcesOutput {
        output: crate::conversions::simple_resource::to_dafny(value.output)
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::resources::internaldafny::types::GetResourcesOutput,
    >,
) -> crate::operation::get_resources::GetResourcesOutput {
    crate::operation::get_resources::GetResourcesOutput {
        output: crate::conversions::simple_resource::from_dafny(dafny_value.output().clone()),
    }
}
