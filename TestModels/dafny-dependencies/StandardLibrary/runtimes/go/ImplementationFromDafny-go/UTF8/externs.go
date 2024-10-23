package UTF8

import (
	"fmt"
	"unicode"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/dafny-lang/DafnyRuntimeGo/v4/dafny"
	"github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
)

//IMP: The below extern implementations are only compatible
//with unicode-char:false transpiled code.

// Decode decodes utf8 encoded Go rune to dafny encoded utf16 char sequence
// Anything we receive here is supposed to be utf8 encoded Go rune.
// And since this extern is for unicode-char:false,
// we need to encode the result in compatible dafny utf16 string before returning
// the result.
func Decode(utf8EncodedDafnySeq dafny.Sequence) Wrappers.Result {
	utf8EncodedByteArray := dafny.ToByteArray(utf8EncodedDafnySeq)

	utf16Encoded := utf16.Encode([]rune(string(utf8EncodedByteArray)))
	var dafnyCharArray []dafny.Char
	for _, c := range utf16Encoded {
		if c == unicode.ReplacementChar {
			err := fmt.Errorf("Encountered Not Allowed Replacement Character: %s ", unicode.ReplacementChar)
			return Wrappers.Companion_Result_.Create_Failure_(dafny.SeqOfString(err.Error()))
		}
		dafnyCharArray = append(dafnyCharArray, dafny.Char(c))
	}
	return Wrappers.Companion_Result_.Default(dafny.SeqOfChars(dafnyCharArray...))
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
