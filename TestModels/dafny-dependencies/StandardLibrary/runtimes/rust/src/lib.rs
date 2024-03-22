#[allow(non_snake_case)]
pub mod UTF8;
pub mod implementation_from_dafny;

#[cfg(test)]
#[allow(non_snake_case)]
mod TestUTF8 {
    use super::*;
    #[test]
    fn TestEncodeHappyCase() {
        let unicodeString = ::dafny_runtime::string_utf16_of("abc\u{0306}\u{01FD}\u{03B2}");
        let expectedBytes =
            dafny_runtime::seq![0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
        let _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&unicodeString);
        if _r.IsFailure() {
            panic!("Encode failed");
        }
        let encoded = _r.Extract();
        assert_eq!(expectedBytes, encoded);
    }

    #[test]
    fn TestEncodeInvalidUnicode() {
        let invalidUnicode = ::dafny_runtime::seq![
            ::dafny_runtime::DafnyCharUTF16('a' as u16),
            ::dafny_runtime::DafnyCharUTF16('b' as u16),
            ::dafny_runtime::DafnyCharUTF16('c' as u16),
            ::dafny_runtime::DafnyCharUTF16(0xD800)
        ];
        let encoded = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&invalidUnicode);
        assert!(encoded.IsFailure());
    }

    #[test]
    fn TestDecodeHappyCase() {
        let unicodeBytes =
            ::dafny_runtime::seq![0x61, 0x62, 0x63, 0xCC, 0x86, 0xC7, 0xBD, 0xCE, 0xB2];
        assert!(
            implementation_from_dafny::r#_UTF8_Compile::_default::Uses2Bytes(
                &::dafny_runtime::seq![0xC7 as u8, 0xBD as u8, 0xCE as u8, 0xB2 as u8]
            )
        );
        assert_eq!(
            ::dafny_runtime::seq![0xC7 as u8, 0xBD as u8, 0xCE as u8, 0xB2 as u8],
            unicodeBytes.slice(&::dafny_runtime::int!(5), &::dafny_runtime::int!(9))
        );
        assert!(
            implementation_from_dafny::r#_UTF8_Compile::_default::ValidUTF8Range(
                &unicodeBytes,
                &::dafny_runtime::int!(7),
                &::dafny_runtime::int!(9)
            )
        );
        assert!(
            implementation_from_dafny::r#_UTF8_Compile::_default::ValidUTF8Range(
                &unicodeBytes,
                &::dafny_runtime::int!(0),
                &::dafny_runtime::int!(9)
            )
        );
        let expectedString = ::dafny_runtime::string_utf16_of("abc\u{0306}\u{01FD}\u{03B2}");
        let _r = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&unicodeBytes);
        if _r.IsFailure() {
            panic!("Decode failed");
        }
        let decoded = _r.Extract();
        assert_eq!(expectedString, decoded);
    }

    #[test]
    fn TestDecodeInvalidUnicode() {
        let invalidUnicode = ::dafny_runtime::seq![
            0x61 as u8, 0x62 as u8, 0x63 as u8, 0xED as u8, 0xA0 as u8, 0x80 as u8
        ];
        let _r = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&invalidUnicode);
        assert!(_r.IsFailure());
    }

    #[test]
    fn Test1Byte() {
        // Null
        let mut decoded = ::dafny_runtime::string_utf16_of("\u{0000}");
        let mut _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        let mut encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x00 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        let mut _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        let mut redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);

        // Space
        decoded = ::dafny_runtime::string_utf16_of(" ");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x20 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);

        decoded = ::dafny_runtime::string_utf16_of("$");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x24 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);

        decoded = ::dafny_runtime::string_utf16_of("0");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x30 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("A");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x41 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("a");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0x61 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses1Byte(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
    }

    #[test]
    fn Test2Bytes() {
        let mut decoded = ::dafny_runtime::string_utf16_of("\u{00A3}");
        let mut _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        let mut encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0xC2 as u8, 0xA3 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses2Bytes(&encoded));
        let mut _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        let mut redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{00A9}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0xC2 as u8, 0xA9 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses2Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{00AE}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0xC2 as u8, 0xAE as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses2Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{03C0}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(::dafny_runtime::seq![0xCF as u8, 0x80 as u8], encoded);
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses2Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
    }

    #[test]
    fn Test3Bytes() {
        let mut decoded = ::dafny_runtime::string_utf16_of("\u{2386}");
        let mut _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        let mut encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xE2 as u8, 0x8E as u8, 0x86 as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses3Bytes(&encoded));
        let mut _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        let mut redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{2387}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xE2 as u8, 0x8E as u8, 0x87 as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses3Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{231B}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xE2 as u8, 0x8C as u8, 0x9B as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses3Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{1D78}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xE1 as u8, 0xB5 as u8, 0xB8 as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses3Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{732B}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xE7 as u8, 0x8C as u8, 0xAB as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses3Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
    }

    #[test]
    fn Test4Bytes() {
        let mut decoded = ::dafny_runtime::seq![
            ::dafny_runtime::DafnyCharUTF16(0xD808),
            ::dafny_runtime::DafnyCharUTF16(0xDC00)
        ];
        let mut _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        println!(
            "{}",
            ::dafny_runtime::DafnyPrintWrapper(&_r.as_ref().clone())
        );
        assert!(!_r.IsFailure());
        let mut encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xF0 as u8, 0x92 as u8, 0x80 as u8, 0x80 as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses4Bytes(&encoded));
        let mut _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        let mut redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
        decoded = ::dafny_runtime::string_utf16_of("\u{1D7C1}");
        _r = implementation_from_dafny::r#_UTF8_Compile::_default::Encode(&decoded);
        assert!(!_r.IsFailure());
        encoded = _r.Extract();
        assert_eq!(
            ::dafny_runtime::seq![0xF0 as u8, 0x9D as u8, 0x9F as u8, 0x81 as u8],
            encoded
        );
        assert!(implementation_from_dafny::r#_UTF8_Compile::_default::Uses4Bytes(&encoded));
        _r2 = implementation_from_dafny::r#_UTF8_Compile::_default::Decode(&encoded);
        assert!(!_r2.IsFailure());
        redecoded = _r2.Extract();
        assert_eq!(decoded, redecoded);
    }
}
