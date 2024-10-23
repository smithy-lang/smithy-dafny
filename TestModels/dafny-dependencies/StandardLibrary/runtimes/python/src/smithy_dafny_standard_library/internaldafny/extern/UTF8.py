"""
Extern UTF8 encode and decode methods.

Note:
Python's `.encode()`/`.decode()` handle surrogates with 'surrogatepass'.
However, the results of 'surrogatepass' does not comply with Dafny's expectations.
Dafny expects a strict interpretation of Python's Unicode handling.
Python represents Unicode characters based on their presence in the Basic Multilingual Plane (BMP).
The BMP includes characters from U+0000 to U+FFFF (or, 0 <= ord(chr) < 65535).

If a character is inside the BMP, Python internally represents it as a single UTF-16-encoded code unit.
ex.
"\u2386" == '⎆' --> ord('⎆') == 9094 --> 9094 < 65535 --> in BMP
Since "\u2386" is in the BMP, Python internally represents it as '⎆':

```
>>> s = "\u2386"
>>> s
'⎆'
```

In contrast, if a character is outside the BMP, Python internally represents it
as a unicode-escaped string using surrogate pairs.
ex.
"\uD808\uDC00" == '𒀀' --> ord('𒀀') == 73728 --> 73728 > 65535 --> outside BMP
Since "\uD808\uDC00" is outside the BMP, Python internally represents it as "\uD808\uDC00":

```
>>> s = "\uD808\uDC00"
>>> s
'\ud808\udc00'
```

However, the `.decode()` method with 'surrogatepass' leaves '\ud808\udc00' as '𒀀',
which does not match Dafny's expectation of the literal interpretation of this field.
To correct this, the Decode extern implementation
re-encodes any characters outside the BMP,
then decodes them under the expected decoding.
"""
import _dafny
import struct

import smithy_dafny_standard_library.internaldafny.generated.UTF8
from smithy_dafny_standard_library.internaldafny.generated.UTF8 import *

def _convert_char_outside_bmp_to_unicode_escaped_string(char_outside_bmp):
  # Re-encode the character to UTF-16. This is necessary to get the surrogate pairs.
  utf16_encoded_char = char_outside_bmp.encode('utf-16')
  # Define the size of the Byte Order Mark (BOM). UTF-16 encoding includes a BOM at the start.
  bom_size = 2
  # Extract and decode the high surrogate pair. The high surrogate is the first 2 bytes after the BOM.
  high_surrogate = utf16_encoded_char[bom_size:bom_size+2].decode('utf-16', 'surrogatepass')
  # Extract and decode the low surrogate pair. The low surrogate is the next 2 bytes after the high surrogate.
  low_surrogate = utf16_encoded_char[bom_size+2:bom_size+4].decode('utf-16', 'surrogatepass')
  # Return the high and low surrogate pairs as a tuple so they can be appended individually.
  return (high_surrogate, low_surrogate)

def _is_outside_bmp(native_char):
  # Any char greater than 0xFFFF is outside the BMP.
  return ord(native_char) > 0xFFFF

# Extend the Dafny-generated class with our extern methods
class default__(smithy_dafny_standard_library.internaldafny.generated.UTF8.default__):

  @staticmethod
  def Encode(s):
    try:
      return Wrappers.Result_Success(_dafny.Seq(
          s.VerbatimString(False).encode('utf-16', 'surrogatepass').decode('utf-16').encode('utf-8')
      ))
    # Catch both UnicodeEncodeError and UnicodeDecodeError.
    # The `try` block involves both encoding and decoding.
    # OverflowError is possibly raised at `_strict_tostring`'s `ord(c).to_bytes`
    # if the char `c` is not valid.
    except (UnicodeDecodeError, UnicodeEncodeError, OverflowError):
      return Wrappers.Result_Failure(_dafny.Seq("Could not encode input to Dafny Bytes."))

  @staticmethod
  def Decode(s):
    try:
      first_pass_decoded = bytes(s).decode('utf-8')
      decoded = []
      for i in range(len(first_pass_decoded)):
        char = first_pass_decoded[i]
        # Dafny-generated code expects any characters outside the BMP
        # to be rendered as unicode-escaped strings.
        if _is_outside_bmp(char):
          # Any char outside the BMP needs to be re-encoded,
          # then decoded as separate bytes.
          high_surrogate, low_surrogate = _convert_char_outside_bmp_to_unicode_escaped_string(char)
          decoded.append(high_surrogate)
          decoded.append(low_surrogate)
        else:
          decoded.append(char)
      return Wrappers.Result_Success(_dafny.Seq(
        decoded
      ))
    except (UnicodeDecodeError, UnicodeEncodeError, ValueError, TypeError, struct.error):
      return Wrappers.Result_Failure(_dafny.Seq("Could not decode input from Dafny Bytes."))


# Export externs
smithy_dafny_standard_library.internaldafny.generated.UTF8.default__ = default__