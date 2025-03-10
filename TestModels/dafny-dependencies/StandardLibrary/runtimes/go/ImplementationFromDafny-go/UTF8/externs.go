package UTF8

import (
	"fmt"
	"unicode"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/aws/aws-cryptographic-material-providers-library/releases/go/smithy-dafny-standard-library/Wrappers"
	"github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
)

//IMP: The below extern implementations are only compatible
//with unicode-char:false transpiled code.

// Decode decodes utf8 encoded Go rune to dafny encoded utf16 char sequence
// Anything we receive here is supposed to be utf8 encoded Go rune.
// And since this extern is for unicode-char:false,
// we need to encode the result in compatible dafny utf16 string before returning
// the result.
func Decode(utf8EncodedDafnySeq dafny.Sequence) Wrappers.Result {
	res, err := DecodeFromNativeGoByteArray(dafny.ToByteArray(utf8EncodedDafnySeq))
	if err != nil {
		return Wrappers.Companion_Result_.Create_Failure_(dafny.SeqOfString(err.Error()))
	}

	return Wrappers.Companion_Result_.Create_Success_(res)
}

// Encode encodes utf16 encoded dafny char (rune) to utf-8 Go rune sequence.
// Anything we receive here is supposed to be utf16 encoded Go rune
// since this extern is for unicode-char:false.
func Encode(utf16EncodedDafnySeq dafny.Sequence) Wrappers.Result {
	encodedUtf16 := utf16EncodedDafnySeqToUint16(utf16EncodedDafnySeq)
	decodedUtf16 := utf16.Decode(encodedUtf16)
	var utf8EncodedBytes []byte
	for _, r := range decodedUtf16 {
		if !utf8.ValidRune(r) || r == unicode.ReplacementChar {
			return Wrappers.Companion_Result_.Create_Failure_(dafny.SeqOfString("Failed to utf8 encode rune"))
		}
		buf := make([]byte, utf8.RuneLen(r))
		n := utf8.EncodeRune(buf, r)
		utf8EncodedBytes = append(utf8EncodedBytes, buf[:n]...)
	}
	return Wrappers.Companion_Result_.Create_Success_(dafny.SeqOfBytes(utf8EncodedBytes))
}

// This method is to be called from the Type Conversion layer.
// We reuse the same method so that all conversions are consistent.
func DecodeFromNativeGoByteArray(utf8EncodedByteArray []byte) (dafny.Sequence, error) {
	if !utf8.Valid(utf8EncodedByteArray) {
		return nil, fmt.Errorf("invalid utf8 encoded sequence: %v", utf8EncodedByteArray)
	}
	utf16Encoded := utf16.Encode([]rune(string(utf8EncodedByteArray)))
	var dafnyCharArray []dafny.Char
	for _, c := range utf16Encoded {
		dafnyCharArray = append(dafnyCharArray, dafny.Char(c))
	}
	return dafny.SeqOfChars(dafnyCharArray...), nil
}

func utf16EncodedDafnySeqToUint16(seq dafny.Sequence) []uint16 {
	var r []uint16
	for i := dafny.Iterate(seq); ; {
		val, ok := i()
		if !ok {
			return r
		} else {
			r = append(r, uint16(val.(dafny.Char)))
		}
	}
}
