// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_constraints::GetConstraintsOutput,
) -> ::std::rc::Rc<
    crate::r#simple::constraints::internaldafny::types::GetConstraintsOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::constraints::internaldafny::types::GetConstraintsOutput::GetConstraintsOutput {
        MyString: crate::standard_library_conversions::ostring_to_dafny(&value.my_string),
 NonEmptyString: crate::standard_library_conversions::ostring_to_dafny(&value.non_empty_string),
 StringLessThanOrEqualToTen: crate::standard_library_conversions::ostring_to_dafny(&value.string_less_than_or_equal_to_ten),
 MyBlob: crate::standard_library_conversions::oblob_to_dafny(&value.my_blob),
 NonEmptyBlob: crate::standard_library_conversions::oblob_to_dafny(&value.non_empty_blob),
 BlobLessThanOrEqualToTen: crate::standard_library_conversions::oblob_to_dafny(&value.blob_less_than_or_equal_to_ten),
 MyList: ::std::rc::Rc::new(match &value.my_list {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&e),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 NonEmptyList: ::std::rc::Rc::new(match &value.non_empty_list {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&e),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 ListLessThanOrEqualToTen: ::std::rc::Rc::new(match &value.list_less_than_or_equal_to_ten {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&e),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 MyMap:
::std::rc::Rc::new(match &value.my_map {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&v),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 NonEmptyMap:
::std::rc::Rc::new(match &value.non_empty_map {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&v),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 MapLessThanOrEqualToTen:
::std::rc::Rc::new(match &value.map_less_than_or_equal_to_ten {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
            |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&k),
            |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&v),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
 OneToTen: crate::standard_library_conversions::oint_to_dafny(value.one_to_ten),
 thatTenToTen: crate::standard_library_conversions::olong_to_dafny(&value.that_ten_to_ten),
 GreaterThanOne: crate::standard_library_conversions::oint_to_dafny(value.greater_than_one),
 LessThanTen: crate::standard_library_conversions::oint_to_dafny(value.less_than_ten),
 MyUtf8Bytes: (match value.my_utf8_bytes {
  Some(s) => crate::_Wrappers_Compile::Option::Some { value: dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&s.as_bytes().to_vec(), |b| *b) },
  None => crate::_Wrappers_Compile::Option::None {},
}).into(),
 MyListOfUtf8Bytes: ::std::rc::Rc::new(match &value.my_list_of_utf8_bytes {
    Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&e.as_bytes().to_vec(), |b| *b),
        )
    },
    None => crate::r#_Wrappers_Compile::Option::None {}
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::constraints::internaldafny::types::GetConstraintsOutput,
    >,
) -> crate::operation::get_constraints::GetConstraintsOutput {
    crate::operation::get_constraints::GetConstraintsOutput::builder()
        .set_my_string(crate::standard_library_conversions::ostring_from_dafny(dafny_value.MyString().clone()))
 .set_non_empty_string(crate::standard_library_conversions::ostring_from_dafny(dafny_value.NonEmptyString().clone()))
 .set_string_less_than_or_equal_to_ten(crate::standard_library_conversions::ostring_from_dafny(dafny_value.StringLessThanOrEqualToTen().clone()))
 .set_my_blob(crate::standard_library_conversions::oblob_from_dafny(dafny_value.MyBlob().clone()))
 .set_non_empty_blob(crate::standard_library_conversions::oblob_from_dafny(dafny_value.NonEmptyBlob().clone()))
 .set_blob_less_than_or_equal_to_ten(crate::standard_library_conversions::oblob_from_dafny(dafny_value.BlobLessThanOrEqualToTen().clone()))
 .set_my_list(match (*dafny_value.MyList()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_non_empty_list(match (*dafny_value.NonEmptyList()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_list_less_than_or_equal_to_ten(match (*dafny_value.ListLessThanOrEqualToTen()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_my_map(match (*dafny_value.MyMap()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(v),
            )
        ),
    _ => None
}
)
 .set_non_empty_map(match (*dafny_value.NonEmptyMap()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(v),
            )
        ),
    _ => None
}
)
 .set_map_less_than_or_equal_to_ten(match (*dafny_value.MapLessThanOrEqualToTen()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(k),
                |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(v),
            )
        ),
    _ => None
}
)
 .set_one_to_ten(crate::standard_library_conversions::oint_from_dafny(dafny_value.OneToTen().clone()))
 .set_that_ten_to_ten(crate::standard_library_conversions::olong_from_dafny(dafny_value.thatTenToTen().clone()))
 .set_greater_than_one(crate::standard_library_conversions::oint_from_dafny(dafny_value.GreaterThanOne().clone()))
 .set_less_than_ten(crate::standard_library_conversions::oint_from_dafny(dafny_value.LessThanTen().clone()))
 .set_my_utf8_bytes(match dafny_value.MyUtf8Bytes().as_ref() {
  crate::_Wrappers_Compile::Option::Some { .. } => ::std::option::Option::Some(::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&dafny_value.MyUtf8Bytes().Extract(), |b| *b)).unwrap()),
  _ => ::std::option::Option::None,
})
 .set_my_list_of_utf8_bytes(match (*dafny_value.MyListOfUtf8Bytes()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| ::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&::std::borrow::Borrow::borrow(e), |b| *b)).unwrap(),
            )
        ),
    _ => None
}
)
        .build()
        .unwrap()
}
