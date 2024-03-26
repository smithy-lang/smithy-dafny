#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
extern crate SimpleString;

#[cfg(test)]
mod SimpleStringImplTest {
  use SimpleString::*;
  use SimpleString::implementation_from_dafny::dafny_runtime;
  /*
  method{:test} GetString(){
        var client :- expect SimpleString.SimpleString();
        TestGetString(client);
        TestGetStringSingleValue(client);
        TestGetStringUTF8(client);
    }
  */

  #[test]
  fn GetString() {
    let _r =
      SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny::_default::SimpleString(
        &::std::rc::Rc::new(SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny::_default::DefaultSimpleStringConfig())
      );
    assert!(!_r.IsFailure());
    let client = _r.Extract();
    TestGetString(client);
    TestGetStringSingleValue(client);
    TestGetStringUTF8(client);
  }

  /*method TestGetString(client: ISimpleTypesStringClient)
    {
        var ret :- expect client.GetString(SimpleString.Types.GetStringInput(value:= Some("TEST_SIMPLE_STRING_VALUE")));
        expect ret.value.UnwrapOr("") == "TEST_SIMPLE_STRING_VALUE";
        print ret;
    } */
  fn TestGetString(client: *mut dyn SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient) {
    let _r = dafny_runtime::read!(client).GetString(
      &::std::rc::Rc::new(SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput::GetStringInput {
        value: ::std::rc::Rc::new(
            SimpleString::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: dafny_runtime::string_utf16_of("TEST_SIMPLE_STRING_VALUE") })
      }),
    );
    assert!(!_r.IsFailure());
    let ret = _r.Extract();
    assert_eq!(ret.value().UnwrapOr(&dafny_runtime::string_utf16_of("")), dafny_runtime::string_utf16_of("TEST_SIMPLE_STRING_VALUE"));
    println!("{:?}", ret);
  }

  fn TestGetStringSingleValue(client: *mut dyn SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient) {
    let _r = dafny_runtime::read!(client).GetStringSingleValue(
      &::std::rc::Rc::new(SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput::GetStringInput {
        value: ::std::rc::Rc::new(
            SimpleString::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: dafny_runtime::string_utf16_of("TEST_SIMPLE_STRING_SINGLE_VALUE") })
      }),
    );
    assert!(!_r.IsFailure());
    let ret = _r.Extract();
    assert_eq!(ret.value().UnwrapOr(&dafny_runtime::string_utf16_of("")), dafny_runtime::string_utf16_of("TEST_SIMPLE_STRING_SINGLE_VALUE"));
    println!("{:?}", ret);
  }

   /*method TestGetStringUTF8(client: ISimpleTypesStringClient)
    {
        // utf8EncodedString holds a value of UTF-8 encoded Hindi word "Anar" (pomegranate, similar to A -> Apple) in it's native script
        var utf8EncodedString := "\u0905\u0928\u093e\u0930";
        var ret :- expect client.GetStringUTF8(SimpleString.Types.GetStringInput(value:= Some(utf8EncodedString)));
        expect ret.value.UnwrapOr("") == utf8EncodedString;
        print ret;
    }*/
  fn TestGetStringUTF8(client: *mut dyn SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::ISimpleTypesStringClient) {
    let utf8EncodedString = dafny_runtime::string_utf16_of("\u{0905}\u{0928}\u{093e}\u{0930}");
    let _r = dafny_runtime::read!(client).GetStringUTF8(
      &::std::rc::Rc::new(SimpleString::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput::GetStringInput {
        value: ::std::rc::Rc::new(
            SimpleString::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: utf8EncodedString.clone() })
      }),
    );
    assert!(!_r.IsFailure());
    let ret = _r.Extract();
    assert_eq!(ret.clone().value().UnwrapOr(&dafny_runtime::string_utf16_of("")), utf8EncodedString.clone());
    println!("{:?}", ret);
  }
}