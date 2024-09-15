// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod client;

impl crate::r#simple::multiplemodels::dependencyproject::internaldafny::wrapped::_default {
  pub fn WrappedDependencyProject(config: &::std::rc::Rc<
      crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig,
  >) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::IDependencyProjectClient>,
          ::std::rc::Rc<crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::Error>
  >>{
      crate::deps::simple_multiplemodels_dependencyproject::wrapped::client::Client::from_conf(config)
  }
}
