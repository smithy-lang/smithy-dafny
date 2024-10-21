// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![deny(warnings, unconditional_panic)]
#![deny(clippy::all)]

use crate::_SimpleExtendableResourcesTest_Compile::ExtendableResource;
use crate::r#_Wrappers_Compile::Result;
use crate::simple::extendable::resources::internaldafny::types::Error;
use crate::simple::extendable::resources::internaldafny::types::GetExtendableResourceDataInput;
use crate::simple::extendable::resources::internaldafny::types::GetExtendableResourceDataOutput;
use crate::simple::extendable::resources::internaldafny::types::GetExtendableResourceErrorsInput;
use crate::simple::extendable::resources::internaldafny::types::GetExtendableResourceErrorsOutput;
use crate::simple::extendable::resources::internaldafny::types::IExtendableResource;
use std::rc::Rc;

pub mod simple {
    pub mod extendable {
        pub mod resources {
            pub mod internaldafny {
                pub mod nativeresourcefactory {
                    pub struct _default {}
                }
            }
        }
    }
}

pub struct NativeResource {
    pub inner: Box<dyn IExtendableResource>,
}

impl dafny_runtime::UpcastObject<dyn std::any::Any> for NativeResource {
    dafny_runtime::UpcastObjectFn!(dyn std::any::Any);
}

impl IExtendableResource for NativeResource {
    fn r#_AlwaysMultipleErrors_k(
        &self,
        input: &Rc<GetExtendableResourceErrorsInput>,
    ) -> Rc<Result<Rc<GetExtendableResourceErrorsOutput>, Rc<Error>>> {
        self.inner._AlwaysMultipleErrors_k(input)
    }
    fn r#_GetExtendableResourceData_k(
        &self,
        input: &Rc<GetExtendableResourceDataInput>,
    ) -> Rc<Result<Rc<GetExtendableResourceDataOutput>, Rc<Error>>> {
        self.inner._GetExtendableResourceData_k(input)
    }
    fn r#_AlwaysModeledError_k(
        &self,
        input: &Rc<GetExtendableResourceErrorsInput>,
    ) -> Rc<Result<Rc<GetExtendableResourceErrorsOutput>, Rc<Error>>> {
        self.inner._AlwaysModeledError_k(input)
    }
    fn r#_AlwaysOpaqueError_k(
        &self,
        input: &Rc<GetExtendableResourceErrorsInput>,
    ) -> Rc<Result<Rc<GetExtendableResourceErrorsOutput>, Rc<Error>>> {
        self.inner._AlwaysOpaqueError_k(input)
    }
}

impl crate::simple::extendable::resources::internaldafny::nativeresourcefactory::_default {
    pub fn DafnyFactory(
    ) -> dafny_runtime::Object<dyn crate::_WrappedTest_Compile::IExtendableResource> {
        let nr = NativeResource {
            inner: Box::new(ExtendableResource {
                __i_name: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string("dafny-default")
            })
        };
        let rcnc = Rc::new(nr);
        unsafe { dafny_runtime::Object::from_rc(rcnc) }
    }
}
