#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
use ::dafny_standard_library::implementation_from_dafny::*;

pub mod r#_TestUTF8_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn TestEncodeHappyCase() -> () {
            let mut unicodeString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(97 as u16),
                ::dafny_runtime::DafnyCharUTF16(98 as u16),
                ::dafny_runtime::DafnyCharUTF16(99 as u16),
                ::dafny_runtime::DafnyCharUTF16(774 as u16),
                ::dafny_runtime::DafnyCharUTF16(509 as u16),
                ::dafny_runtime::DafnyCharUTF16(946 as u16)
            ];
            let mut expectedBytes: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![97, 98, 99, 204, 134, 199, 189, 206, 178];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&unicodeString));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: super::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            if !(expectedBytes.clone() == encoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn TestEncodeInvalidUnicode() -> () {
            let mut invalidUnicode: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(97 as u16),
                ::dafny_runtime::DafnyCharUTF16(98 as u16),
                ::dafny_runtime::DafnyCharUTF16(99 as u16),
                ::dafny_runtime::DafnyCharUTF16(55296 as u16)
            ];
            let mut encoded: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Result<
                    super::UTF8::ValidUTF8Bytes,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = super::UTF8::_default::Encode(&invalidUnicode);
            if !matches!(
                (&encoded).as_ref(),
                super::r#_Wrappers_Compile::Result::Failure { .. }
            ) {
                panic!("Halt")
            };
            return ();
        }
        pub fn TestDecodeHappyCase() -> () {
            let mut unicodeBytes: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![97, 98, 99, 204, 134, 199, 189, 206, 178];
            let mut expectedString: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(97 as u16),
                ::dafny_runtime::DafnyCharUTF16(98 as u16),
                ::dafny_runtime::DafnyCharUTF16(99 as u16),
                ::dafny_runtime::DafnyCharUTF16(774 as u16),
                ::dafny_runtime::DafnyCharUTF16(509 as u16),
                ::dafny_runtime::DafnyCharUTF16(946 as u16)
            ];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&unicodeBytes));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError0.read().Extract();
            if !(expectedString.clone() == decoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn TestDecodeInvalidUnicode() -> () {
            let mut invalidUnicode: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![97, 98, 99, 237, 160, 128];
            if !(!super::UTF8::_default::ValidUTF8Seq(&invalidUnicode)) {
                panic!("Halt")
            };
            if !matches!(
                (&super::UTF8::_default::Decode(&invalidUnicode)).as_ref(),
                super::r#_Wrappers_Compile::Result::Failure { .. }
            ) {
                panic!("Halt")
            };
            return ();
        }
        pub fn Test1Byte() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(0 as u16)];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: super::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            if !(::dafny_runtime::seq![0] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(32 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            if !(::dafny_runtime::seq![32] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("$");
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            if !(::dafny_runtime::seq![36] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("0");
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            if !(::dafny_runtime::seq![48] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("A");
            let mut valueOrError8 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError8 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError8.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError8.read().Extract();
            if !(::dafny_runtime::seq![65] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError9 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError9 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError9.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError9.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("a");
            let mut valueOrError10 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError10 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError10.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError10.read().Extract();
            if !(::dafny_runtime::seq![97] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError11 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError11 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError11.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError11.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn Test2Bytes() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(163 as u16)];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: super::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            if !(::dafny_runtime::seq![194, 163] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(169 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            if !(::dafny_runtime::seq![194, 169] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(174 as u16)];
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            if !(::dafny_runtime::seq![194, 174] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(960 as u16)];
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            if !(::dafny_runtime::seq![207, 128] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn Test3Bytes() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(9094 as u16)];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: super::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            if !(::dafny_runtime::seq![226, 142, 134] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(9095 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            if !(::dafny_runtime::seq![226, 142, 135] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(8987 as u16)];
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            if !(::dafny_runtime::seq![226, 140, 155] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(7544 as u16)];
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            if !(::dafny_runtime::seq![225, 181, 184] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(29483 as u16)];
            let mut valueOrError8 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError8 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError8.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError8.read().Extract();
            if !(::dafny_runtime::seq![231, 140, 171] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError9 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError9 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError9.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError9.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn Test4Bytes() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(55304 as u16),
                ::dafny_runtime::DafnyCharUTF16(56320 as u16)
            ];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: super::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            if !(::dafny_runtime::seq![240, 146, 128, 128] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses4Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(55349 as u16),
                ::dafny_runtime::DafnyCharUTF16(57281 as u16)
            ];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        super::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            if !(::dafny_runtime::seq![240, 157, 159, 129] == encoded.clone()) {
                panic!("Halt")
            };
            if !super::UTF8::_default::Uses4Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    super::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(super::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            if !(decoded.clone() == redecoded.clone()) {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::r#_TestUTF8_Compile::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.TestEncodeHappyCase: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::TestEncodeHappyCase();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.TestEncodeInvalidUnicode: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::TestEncodeInvalidUnicode();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.TestDecodeHappyCase: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::TestDecodeHappyCase();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.TestDecodeInvalidUnicode: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::TestDecodeInvalidUnicode();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.Test1Byte: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::Test1Byte();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.Test2Bytes: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::Test2Bytes();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.Test3Bytes: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::Test3Bytes();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.Test4Bytes: "#
                ))
            );
            super::r#_TestUTF8_Compile::_default::Test4Bytes();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::_module::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
fn main() {
    _module::_default::_Test__Main_();
}
