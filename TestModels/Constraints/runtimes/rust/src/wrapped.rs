// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod client;

impl crate::r#simple::constraints::internaldafny::wrapped::_default {
  pub fn WrappedSimpleConstraints(config: &::std::rc::Rc<
      crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig,
  >) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::r#simple::constraints::internaldafny::types::ISimpleConstraintsClient>,
          ::std::rc::Rc<crate::r#simple::constraints::internaldafny::types::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
