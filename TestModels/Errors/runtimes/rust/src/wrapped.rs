// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod client;

impl crate::r#simple::errors::internaldafny::wrapped::_default {
  pub fn WrappedSimpleErrors(config: &::std::rc::Rc<
      crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig,
  >) -> ::std::rc::Rc<crate::r#_Wrappers_Compile::Result<
          ::dafny_runtime::Object<dyn crate::r#simple::errors::internaldafny::types::ISimpleErrorsClient>,
          ::std::rc::Rc<crate::r#simple::errors::internaldafny::types::Error>
  >>{
      crate::wrapped::client::Client::from_conf(config)
  }
}
