from standard_library.internaldafny.generated.UTF8 import *
import standard_library.internaldafny.generated.UTF8
import _dafny
import struct

'''
Extern UTF8 encode and decode methods.

Note:
Python's `.encode('utf-8')` does not handle surrogates.
However, these encode/decode methods are expected to handle surrogates (e.g. "\uD808\uDC00").
To work around this, we encode Dafny strings into UTF-16-LE (little endian)
and decode them before encoding into UTF-8 (`_strict_tostring`).
To decode, we reverse the encode step. (`_reverse_strict_tostring`)
'''

# Extend the Dafny-generated class with our extern methods
class default__(standard_library.internaldafny.generated.UTF8.default__):

  @staticmethod
  def Encode(s):
    try:
      return Wrappers.Result_Success(_dafny.Seq(
          default__._strict_tostring(s).encode('utf-8')
      ))
    # Catch both UnicodeEncodeError and UnicodeDecodeError.
    # The `try` block involves both encoding and decoding.
    # OverflowError is possibly raised at `_strict_tostring`'s `ord(c).to_bytes`
    #   if the char `c` is not valid.
    except (UnicodeDecodeError, UnicodeEncodeError, OverflowError):
      return Wrappers.Result_Failure(_dafny.Seq("Could not encode input to Dafny Bytes."))

  @staticmethod
  def _strict_tostring(dafny_ascii_string):
    '''
    Converts a Dafny Seq of unicode-escaped ASCII characters
    into a string that can be encoded with Python's built-in `.encode('utf-8')`.

    This encoding-decoding allows subsequent UTF8 encodings
    to handle surrogates as expected by Dafny code.

    This is exactly the `_dafny.string_from_utf_16` method from the DafnyRuntime, except with
    `errors = 'strict'` here,
    instead of
    `errors = 'replace'` in the `_dafny.string_from_utf_16` function.
    `strict` will throw an exception for invalid encodings, allowing us
    to detect invalid encodings and raise exceptions,
    while `replace` will fail silently.
    :param s:
    :return:
    '''
    return b''.join(ord(c).to_bytes(2, 'little') for c in dafny_ascii_string).decode("utf-16-le", errors = 'strict')

  @staticmethod
  def Decode(s):
    try:
      utf8_str = bytes(s).decode('utf-8')
      unicode_escaped_utf8_str = default__._reverse_strict_tostring(utf8_str)
      return Wrappers.Result_Success(unicode_escaped_utf8_str)
    # Catch both UnicodeEncodeError and UnicodeDecodeError.
    # The `try` block involves both encoding and decoding.
    # ValueError and TypeError are possibly raised at `_reverse_strict_tostring`'s `chr()`.
    # struct.error is possibly raised at `struct.unpack`.
    except (UnicodeDecodeError, UnicodeEncodeError, ValueError, TypeError, struct.error):
      return Wrappers.Result_Failure(_dafny.Seq("Could not decode input from Dafny Bytes."))


  @staticmethod
  def _reverse_strict_tostring(utf8_str):
    '''
    Converts a string into a Dafny Seq of unicode-escaped ASCII characters.
    This is the inverse of the `_strict_tostring` function in this file.
    :param s:
    :return:
    '''
    utf16_bytes = utf8_str.encode("utf-16-le", errors = "strict")
    out = []
    # len(b)/2 is an integer by construction of UTF-16 encoding (2 bytes per encoded character)
    for i in range(int(len(utf16_bytes)/2)):
      # Take two consecutive bytes;
      utf_16_bytepair = utf16_bytes[2*i:2*i+2]
      # Unpack them into an ordinal representation;
      packed_bytes = struct.unpack('<H', utf_16_bytepair)
      # Convert into a character representation;
      char_representation = chr(packed_bytes[0])
      # Append to returned string
      out.append(char_representation)
    return _dafny.Seq(out)

standard_library.internaldafny.generated.UTF8.default__ = default__