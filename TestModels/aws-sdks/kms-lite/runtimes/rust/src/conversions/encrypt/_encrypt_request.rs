// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.EncryptInput
#[allow(dead_code)]
pub fn to_dafny(
    value: aws_sdk_kms::operation::encrypt::EncryptInput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest::EncryptRequest  {
        Plaintext: dafny_standard_library::conversion::oblob_to_dafny(&value.plaintext).Extract(),
        KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id).Extract(),
        EncryptionContext: 
        ::std::rc::Rc::new(match value.encryption_context() {
            Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
                ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
                    |k| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(k),
                    |v| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(v),
                )
            },
            None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
        }),
        GrantTokens:
        ::std::rc::Rc::new(
            // Have to clone or else this becomes a borrow that can interfere with other branches
            match value.grant_tokens.clone() {
                Some(val) =>
                crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some {
                        value : ::dafny_runtime::Sequence::from_array(
                            &val.iter().map(|x|
                                dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(x))
                                .collect()
                        )
                    },
                None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None{}
            }
        ),
        DryRun: dafny_standard_library::conversion::obool_to_dafny(&value.dry_run),
        EncryptionAlgorithm: ::std::rc::Rc::new(match value.encryption_algorithm {
            Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x) },
            None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
        })
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest,
    >,
    client: aws_sdk_kms::Client,
) -> aws_sdk_kms::operation::encrypt::builders::EncryptFluentBuilder {
    client.encrypt()
        .set_plaintext(Some(dafny_standard_library::conversion::blob_from_dafny(dafny_value.Plaintext().clone())))
        .set_key_id(Some(
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.KeyId())),
        )
        .set_encryption_context( match (*dafny_value.EncryptionContext()).as_ref() {
            crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
                Some(
                    ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                        dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string,
                        dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string,
                    )
                ),
            _ => None
        })
        .set_grant_tokens(match  &**dafny_value.GrantTokens() {
            crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
                Some(
                    ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value, 
                        dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string)
                ),
            _ => None
        })
        .set_dry_run(dafny_standard_library::conversion::obool_from_dafny(dafny_value.DryRun().clone()))
        .set_encryption_algorithm(
            dafny_standard_library::conversion::option_from_dafny(
                dafny_value.EncryptionAlgorithm().clone(), 
                |x| crate::conversions::encryption_algorithm_spec::from_dafny(x)))
}
