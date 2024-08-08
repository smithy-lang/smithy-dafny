#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_TestUTF8_Compile {
    pub struct _default {}

    impl _default {
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
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&unicodeString));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: crate::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            let mut _e00: ::dafny_runtime::Sequence<u8> = expectedBytes.clone();
            let mut _e10: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e00.clone() == _e10.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e00));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e10));
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
                crate::r#_Wrappers_Compile::Result<
                    crate::UTF8::ValidUTF8Bytes,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = crate::UTF8::_default::Encode(&invalidUnicode);
            if !matches!(
                (&encoded).as_ref(),
                crate::r#_Wrappers_Compile::Result::Failure { .. }
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
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&unicodeBytes));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError0.read().Extract();
            let mut _e01: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                expectedString.clone();
            let mut _e11: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            if !(_e01.clone() == _e11.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e01));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e11));
                panic!("Halt")
            };
            return ();
        }
        pub fn TestDecodeInvalidUnicode() -> () {
            let mut invalidUnicode: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![97, 98, 99, 237, 160, 128];
            if !(!crate::UTF8::_default::ValidUTF8Seq(&invalidUnicode)) {
                panic!("Halt")
            };
            if !matches!(
                (&crate::UTF8::_default::Decode(&invalidUnicode)).as_ref(),
                crate::r#_Wrappers_Compile::Result::Failure { .. }
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
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: crate::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            let mut _e02: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![0];
            let mut _e12: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e02.clone() == _e12.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e02));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e12));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            let mut _e03: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e13: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e03.clone() == _e13.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e03));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e13));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(32 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            let mut _e04: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![32];
            let mut _e14: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e04.clone() == _e14.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e04));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e14));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            let mut _e05: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e15: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e05.clone() == _e15.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e05));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e15));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("$");
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            let mut _e06: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![36];
            let mut _e16: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e06.clone() == _e16.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e06));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e16));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            let mut _e07: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e17: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e07.clone() == _e17.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e07));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e17));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("0");
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            let mut _e08: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![48];
            let mut _e18: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e08.clone() == _e18.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e08));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e18));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            let mut _e09: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e19: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e09.clone() == _e19.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e09));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e19));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("A");
            let mut valueOrError8 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError8 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError8.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError8.read().Extract();
            let mut _e010: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![65];
            let mut _e110: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e010.clone() == _e110.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e010));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e110));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError9 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError9 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError9.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError9.read().Extract();
            let mut _e011: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e111: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e011.clone() == _e111.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e011));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e111));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::string_utf16_of("a");
            let mut valueOrError10 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError10 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError10.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError10.read().Extract();
            let mut _e012: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![97];
            let mut _e112: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e012.clone() == _e112.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e012));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e112));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses1Byte(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError11 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError11 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError11.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError11.read().Extract();
            let mut _e013: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e113: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e013.clone() == _e113.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e013));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e113));
                panic!("Halt")
            };
            return ();
        }
        pub fn Test2Bytes() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(163 as u16)];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: crate::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            let mut _e014: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![194, 163];
            let mut _e114: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e014.clone() == _e114.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e014));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e114));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            let mut _e015: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e115: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e015.clone() == _e115.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e015));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e115));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(169 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            let mut _e016: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![194, 169];
            let mut _e116: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e016.clone() == _e116.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e016));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e116));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            let mut _e017: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e117: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e017.clone() == _e117.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e017));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e117));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(174 as u16)];
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            let mut _e018: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![194, 174];
            let mut _e118: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e018.clone() == _e118.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e018));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e118));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            let mut _e019: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e119: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e019.clone() == _e119.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e019));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e119));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(960 as u16)];
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            let mut _e020: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![207, 128];
            let mut _e120: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e020.clone() == _e120.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e020));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e120));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses2Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            let mut _e021: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e121: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e021.clone() == _e121.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e021));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e121));
                panic!("Halt")
            };
            return ();
        }
        pub fn Test3Bytes() -> () {
            let mut decoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(9094 as u16)];
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: crate::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            let mut _e022: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![226, 142, 134];
            let mut _e122: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e022.clone() == _e122.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e022));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e122));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            let mut _e023: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e123: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e023.clone() == _e123.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e023));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e123));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(9095 as u16)];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            let mut _e024: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![226, 142, 135];
            let mut _e124: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e024.clone() == _e124.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e024));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e124));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            let mut _e025: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e125: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e025.clone() == _e125.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e025));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e125));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(8987 as u16)];
            let mut valueOrError4 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError4 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError4.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError4.read().Extract();
            let mut _e026: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![226, 140, 155];
            let mut _e126: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e026.clone() == _e126.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e026));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e126));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError5 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError5 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError5.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError5.read().Extract();
            let mut _e027: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e127: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e027.clone() == _e127.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e027));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e127));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(7544 as u16)];
            let mut valueOrError6 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError6 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError6.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError6.read().Extract();
            let mut _e028: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![225, 181, 184];
            let mut _e128: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e028.clone() == _e128.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e028));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e128));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError7 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError7 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError7.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError7.read().Extract();
            let mut _e029: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e129: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e029.clone() == _e129.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e029));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e129));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![::dafny_runtime::DafnyCharUTF16(29483 as u16)];
            let mut valueOrError8 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError8 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError8.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError8.read().Extract();
            let mut _e030: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![231, 140, 171];
            let mut _e130: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e030.clone() == _e130.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e030));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e130));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses3Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError9 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError9 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError9.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError9.read().Extract();
            let mut _e031: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e131: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e031.clone() == _e131.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e031));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e131));
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
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError0 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut encoded: crate::UTF8::ValidUTF8Bytes = valueOrError0.read().Extract();
            let mut _e032: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![240, 146, 128, 128];
            let mut _e132: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e032.clone() == _e132.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e032));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e132));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses4Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError1 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError1 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError1.read().IsFailure()) {
                panic!("Halt")
            };
            let mut redecoded: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                valueOrError1.read().Extract();
            let mut _e033: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e133: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e033.clone() == _e133.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e033));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e133));
                panic!("Halt")
            };
            decoded = ::dafny_runtime::seq![
                ::dafny_runtime::DafnyCharUTF16(55349 as u16),
                ::dafny_runtime::DafnyCharUTF16(57281 as u16)
            ];
            let mut valueOrError2 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        crate::UTF8::ValidUTF8Bytes,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError2 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Encode(&decoded));
            if !(!valueOrError2.read().IsFailure()) {
                panic!("Halt")
            };
            encoded = valueOrError2.read().Extract();
            let mut _e034: ::dafny_runtime::Sequence<u8> =
                ::dafny_runtime::seq![240, 157, 159, 129];
            let mut _e134: crate::UTF8::ValidUTF8Bytes = encoded.clone();
            if !(_e034.clone() == _e134.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e034));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e134));
                panic!("Halt")
            };
            if !crate::UTF8::_default::Uses4Bytes(&encoded) {
                panic!("Halt")
            };
            let mut valueOrError3 = ::dafny_runtime::MaybePlacebo::<
                ::std::rc::Rc<
                    crate::r#_Wrappers_Compile::Result<
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    >,
                >,
            >::new();
            valueOrError3 =
                ::dafny_runtime::MaybePlacebo::from(crate::UTF8::_default::Decode(&encoded));
            if !(!valueOrError3.read().IsFailure()) {
                panic!("Halt")
            };
            redecoded = valueOrError3.read().Extract();
            let mut _e035: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                decoded.clone();
            let mut _e135: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> =
                redecoded.clone();
            if !(_e035.clone() == _e135.clone()) {
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Left:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e035));
                print!(
                    "{}",
                    ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                        "Right:\n"
                    ))
                );
                print!("{}", ::dafny_runtime::DafnyPrintWrapper(&_e135));
                panic!("Halt")
            };
            return ();
        }
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestUTF8.TestEncodeHappyCase: "#
                ))
            );
            crate::r#_TestUTF8_Compile::_default::TestEncodeHappyCase();
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
            crate::r#_TestUTF8_Compile::_default::TestEncodeInvalidUnicode();
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
            crate::r#_TestUTF8_Compile::_default::TestDecodeHappyCase();
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
            crate::r#_TestUTF8_Compile::_default::TestDecodeInvalidUnicode();
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
            crate::r#_TestUTF8_Compile::_default::Test1Byte();
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
            crate::r#_TestUTF8_Compile::_default::Test2Bytes();
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
            crate::r#_TestUTF8_Compile::_default::Test3Bytes();
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
            crate::r#_TestUTF8_Compile::_default::Test4Bytes();
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
}
fn main() {
    _module::_default::_Test__Main_();
}
