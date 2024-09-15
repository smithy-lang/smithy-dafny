// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::some_dependency_operation::SomeDependencyOperationInput,
) -> ::std::rc::Rc<
    crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::SomeDependencyOperationInput,
>{
    ::std::rc::Rc::new(crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::SomeDependencyOperationInput::SomeDependencyOperationInput {

    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::SomeDependencyOperationInput,
    >,
) -> crate::operation::some_dependency_operation::SomeDependencyOperationInput {
    crate::operation::some_dependency_operation::SomeDependencyOperationInput::builder()

        .build()
        .unwrap()
}
