// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_string_utf8::GetStringUtf8Input,
) -> ::std::rc::Rc<
    crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Input,
>{
    ::std::rc::Rc::new(crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Input::GetStringUTF8Input {
        value: ::std::rc::Rc::new(match value.value {
  Some(s) => crate::_Wrappers_Compile::Option::Some { value: dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&s.as_bytes().to_vec(), |b| *b) },
  None => crate::_Wrappers_Compile::Option::None {},
}),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::smithystring::internaldafny::types::GetStringUTF8Input,
    >,
) -> crate::operation::get_string_utf8::GetStringUtf8Input {
    crate::operation::get_string_utf8::GetStringUtf8Input::builder()
        .set_value(match dafny_value.value().as_ref() {
  crate::_Wrappers_Compile::Option::Some { .. } => ::std::option::Option::Some(::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&dafny_value.value().Extract(), |b| *b)).unwrap()),
  _ => ::std::option::Option::None,
})
        .build()
        .unwrap()
}
