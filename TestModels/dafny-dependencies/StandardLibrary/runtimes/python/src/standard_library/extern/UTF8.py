from standard_library.internal_generated_dafny.UTF8 import *
import standard_library.internal_generated_dafny.UTF8
import _dafny
import struct

'''
Extern UTF8 encode and decode methods.

Note:
Python's `.encode('utf-8')` does not handle surrogates.
These methods are expected to handle surrogates (e.g. "\uD808\uDC00").
To work around this, we encode Dafny strings into UTF-16-LE (little endian)
and decode them before encoding into UTF-8 (`_strict_tostring`).
To decode, we reverse the encode step. (`_reverse_strict_tostring`)
'''

# Extend the Dafny-generated class with our extern methods
class default__(standard_library.internal_generated_dafny.UTF8.default__):

  @staticmethod
  def Encode(s):
    try:
      return Wrappers.Result_Success(_dafny.Seq(
          default__._strict_tostring(s).encode('utf-8')
      ))
    # Catch both Encode and Decode errors.
    # The `try` block involves both encoding and decoding.
    except (UnicodeEncodeError, UnicodeDecodeError):
      return Wrappers.Result_Failure(_dafny.Seq("Could not encode input to Dafny Bytes."))

  @staticmethod
  def _strict_tostring(s):
    '''
    Converts a Dafny Seq of ASCII characters
    into a string by writing a UTF-16-LE decoding,
    then decoding it to ASCII with `strict` encoding.

    This encoding-decoding allows subsequent ASCII-to-UTF8 encodings
    to handle surrogates as expected by Dafny code.

    This is exactly the `_dafny.string_from_utf_16` method, except with
    `errors = 'strict'` in our code
    instead of
    `errors = 'replace'` in the `_dafny.string_from_utf_16` function.
    `strict` will throw an exception for invalid encodings, allowing us
    to detect invalid encodings and raise exceptions.
    :param s:
    :return:
    '''
    return b''.join(ord(c).to_bytes(2, 'little') for c in s).decode("utf-16-le", errors = 'strict')

  @staticmethod
  def Decode(s):
    try:
      a = bytes(s).decode('utf-8')
      out = default__._reverse_strict_tostring(a)
      return Wrappers.Result_Success(out)
    # Catch both Encode and Decode errors.
    # The `try` block involves both encoding and decoding.
    except (UnicodeDecodeError, UnicodeEncodeError):
      return Wrappers.Result_Failure(_dafny.Seq("Could not decode input from Dafny Bytes."))


  @staticmethod
  def _reverse_strict_tostring(s):
    '''
    Converts a string into a Dafny Seq of ASCII characters.
    This will undo the `_strict_tostring` function in this file.
    :param s:
    :return:
    '''
    b = s.encode("utf-16-le", errors = "strict")
    out = []
    # len(b)/2 is an integer by construction of UTF-16 encoding (2 bytes per encoded character)
    for i in range(int(len(b)/2)):
      # Take two consecutive bytes;
      c = b[2*i:2*i+2]
      # Unpack them into an ordinal representation;
      d = struct.unpack('<H', c)
      # Convert into a character representation;
      e = chr(d[0])
      # Append to returned string
      out.append(e)
    return _dafny.Seq(out)

standard_library.internal_generated_dafny.UTF8.default__ = default__