// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::r#_Wrappers_Compile::Result;
use dafny_runtime::rcmut;
use dafny_runtime::Rc;
use std::cell::UnsafeCell;

pub mod internal_ExternDefinitions_Compile {

    use crate::conversions::*;
    use crate::implementation_from_dafny::_ExternDefinitions_Compile::_default;
    use crate::implementation_from_dafny::_OrphanedResource_Compile::*;
    use crate::simple::orphaned::internaldafny::types as internaldafny_types;
    use crate::simple::orphaned::internaldafny::types::*;
    use crate::types::*;
    use dafny_runtime::Rc;

    impl _default {
        pub fn InitializeOrphanedStructure(
            uninitialized_structure: &Rc<internaldafny_types::OrphanedStructure>,
        ) -> Rc<internaldafny_types::OrphanedStructure> {
            let native_structure = orphaned_structure::from_dafny(uninitialized_structure.clone());
            // I don't think generated Rust objects have a "toBuilder" method.
            // Ideally, this extern would convert the Dafny structure to native,
            // then set this property on the converted native structure.
            // But that is sort of outside the scope of this TestModel.
            // The important fact is that the from/to_dafny conversions above and below exist.
            let native_structure_new = crate::types::OrphanedStructure::builder().set_string_value(Some(
                "the extern MUST use Smithy-generated conversions to set this value in the native structure".to_string()
            )).build().unwrap();
            return orphaned_structure::to_dafny(&native_structure_new);
        }

        pub fn CallNativeOrphanedResource(
            dafny_resource: &Object<dyn IOrphanedResource>,
        ) -> Rc<Result<Rc<internaldafny_types::OrphanedResourceOperationOutput>, Rc<Error>>>
        {
            let native_resource_ref =
                crate::conversions::orphaned_resource::from_dafny(dafny_resource.clone());
            let native_resource = native_resource_ref.inner.lock().unwrap();
            let native_output = native_resource.orphaned_resource_operation(
                crate::operation::orphaned_resource_operation::OrphanedResourceOperationInput {
                    some_string: std::option::Option::Some(
                        "the extern MUST provide this string to the native resource's operation"
                            .to_string(),
                    ),
                },
            );

            let dafny_output =
                orphaned_resource_operation::_orphaned_resource_operation_output::to_dafny(
                    native_output.unwrap(),
                );

            Rc::new(Result::<
                Rc<internaldafny_types::OrphanedResourceOperationOutput>,
                Rc<Error>,
            >::Success {
                value: dafny_output,
            })
        }

        pub fn CallNativeOrphanedError(dafny_error: &Rc<Error>) -> Rc<Error> {
            let native_error = crate::conversions::error::from_dafny(dafny_error.clone());
            // I don't think generated Rust objects have a way for me to update the message
            // on a pre-existing object (i.e. public fields or a .toBuilder).
            // Ideally, this extern would convert the Dafny structure to native,
            // then set this property on the converted native structure.
            // But that is sort of outside the scope of this TestModel.
            // The fact that the from/to_dafny conversions above and below exist are the important things.
            let native_error_new = crate::types::error::Error::OrphanedError {
               message : "the extern MUST set this string using the catch-all error converter, NOT the orphaned error-specific converter".to_string()
            };
            return crate::conversions::error::to_dafny(native_error_new);
        }
    }
}
