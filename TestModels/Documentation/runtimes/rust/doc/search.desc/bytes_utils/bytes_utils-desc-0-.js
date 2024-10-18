searchState.loadedDescShard("bytes_utils", 0, "Extra utilities for the bytes crate.\nA concatenation of multiple buffers into a large one, …\nA consumable view of a sequence of buffers.\nThe format macro, but returning Str.\nThe format macro, but returning StrMut.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns the yet unconsumed sequence of buffers.\nCreates a new buffer out of a slice of buffers.\nCreates a new empty instance.\nExtends the buffer by another segment.\nReturns the number of segments (buffers) this contains.\nString-like wrappers around Bytes and BytesMut.\nMove backwards in the string.\nManual splitting iterator.\nA type that can be used to build the storage incrementally.\nDirection of iteration.\nMove forward (in the normal direction) in the string.\nAn immutable counter-part storage.\nThe backing storage for StrInner\nTrait for extra functionality of a mutable storage.\nAn immutable variant of Bytes-backed string.\nImplementation of the Str and StrMut types.\nA mutable variant of BytesMut-backed string.\nError when creating Str or StrMut from invalid UTF8 data.\nTurns the mutable variant into an immutable one.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nConverts the creator (mutable storage) to self.\nCreates an instance from an existing byte storage.\nSame as from_inner, but without the checks.\nCreate <code>Str</code> from static string in O(1).\nCreate <code>Str</code> from static string in O(1).\nAccess to the inner storage.\nProvides mutable access to the inner buffer.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns the byte buffer back to the caller.\nExtracts the inner byte storage.\nSplits into lines.\nA constructor of the iterator.\nCreates an empty instance.\nAppends one character.\nAdds some more bytes to the end of the storage.\nAppends a string.\nA reverse version of split_bytes.\nA reverse version of splitn_bytes.\nExtracts a subslice of the string as an owned Str.\nExtracts a subslice of the string as an owned Str.\nExtracts owned representation of the slice passed.\nExtracts owned representation of the slice passed.\nSplits into whitespace separated “words”.\nSplits the storage at the given byte index and creates two …\nSplits the string into two at the given index.\nSplits and returns the part of already built string, but …\nSplits and returns the part of already built string, but …\nSplits with the provided separator.\nSplits into whitespace separated “words”.\nSplits max. <code>n</code> times according to the given pattern.\nThe inner description of why the data is invalid UTF8.")