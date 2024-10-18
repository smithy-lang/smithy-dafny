searchState.loadedDescShard("documentation", 0, "Common errors and error handling utilities.\nAll operations that this crate can perform.\nA trait for giving a type a useful default value.\nDerive macro generating an impl of the trait <code>Default</code>.\nA single-threaded reference-counting pointer. ‘Rc’ …\nReturns the “default value” for a type.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nUsed to do a cheap reference-to-reference conversion.\n<code>?</code> formatting.\nDerive macro generating an impl of the trait <code>Debug</code>.\nA trait for giving a type a useful default value.\nDerive macro generating an impl of the trait <code>Default</code>.\nTrait for comparisons corresponding to equivalence …\nDerive macro generating an impl of the trait <code>Eq</code>.\nConfiguration for formatting.\nA hashable type.\nDerive macro generating an impl of the trait <code>Hash</code>.\nA trait for hashing an arbitrary stream of bytes.\nA single-threaded reference-counting pointer. ‘Rc’ …\nConverts this type into a shared reference of the (usually …\nReturns the “default value” for a type.\nReturns the hash value for the values written so far.\nFormats the value using the given formatter.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nFeeds this value into the given <code>Hasher</code>.\nFeeds a slice of this type into the given <code>Hasher</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nWrites some data into this <code>Hasher</code>.\nWrites a single <code>i128</code> into this hasher.\nWrites a single <code>i16</code> into this hasher.\nWrites a single <code>i32</code> into this hasher.\nWrites a single <code>i64</code> into this hasher.\nWrites a single <code>i8</code> into this hasher.\nWrites a single <code>isize</code> into this hasher.\nWrites a length prefix into this hasher, as part of being …\nWrites a single <code>str</code> into this hasher.\nWrites a single <code>u128</code> into this hasher.\nWrites a single <code>u16</code> into this hasher.\nWrites a single <code>u32</code> into this hasher.\nWrites a single <code>u64</code> into this hasher.\nWrites a single <code>u8</code> into this hasher.\nWrites a single <code>usize</code> into this hasher.\nA trait to emulate dynamic typing.\nA single-threaded reference-counting pointer. ‘Rc’ …\nForwards to the method defined on the type <code>dyn Any</code>.\nReturns some mutable reference to the inner value if it is …\nForwards to the method defined on the type <code>Any</code>.\nReturns a mutable reference to the inner value as type …\nForwards to the method defined on the type <code>Any</code>.\nForwards to the method defined on the type <code>dyn Any</code>.\nForwards to the method defined on the type <code>Any</code>.\nForwards to the method defined on the type <code>dyn Any</code>.\nReturns some reference to the inner value if it is of type …\nReturns a reference to the inner value as type <code>dyn T</code>.\nForwards to the method defined on the type <code>dyn Any</code>.\nForwards to the method defined on the type <code>Any</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nForwards to the method defined on the type <code>Any</code>.\nForwards to the method defined on the type <code>dyn Any</code>.\nReturns <code>true</code> if the inner type is the same as <code>T</code>.\nGets the <code>TypeId</code> of <code>self</code>.\nA wrapper type to construct uninitialized instances of <code>T</code>.\nA single-threaded reference-counting pointer. ‘Rc’ …\nDefines an additive identity element for <code>Self</code>.\nExtracts the values from an array of <code>MaybeUninit</code> …\nReturns the contents of this <code>MaybeUninit</code> as a slice of …\nReturns the contents of this <code>MaybeUninit</code> as a mutable …\nGets a mutable pointer to the contained value. Reading …\nGets a pointer to the contained value. Reading from this …\nExtracts the value from the <code>MaybeUninit&lt;T&gt;</code> container. This …\nDrops the contained value in place.\nGets a mutable (unique) reference to the contained value.\nReads the value from the <code>MaybeUninit&lt;T&gt;</code> container. The …\nGets a shared reference to the contained value.\nClones the elements from <code>src</code> to <code>this</code>, returning a mutable …\nCopies the elements from <code>src</code> to <code>this</code>, returning a mutable …\nFills <code>this</code> with elements by cloning <code>value</code>, returning a …\nFills <code>this</code> with elements yielded by an iterator until …\nFills <code>this</code> with elements returned by calling a closure …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns <code>true</code> if <code>self</code> is equal to the additive identity.\nCreates a new <code>MaybeUninit&lt;T&gt;</code> initialized with the given …\nSets <code>self</code> to the additive identity element of <code>Self</code>, <code>0</code>.\nReturns the contents of this slice of <code>MaybeUninit</code> as a …\nReturns the contents of this mutable slice of <code>MaybeUninit</code> …\nGets a mutable pointer to the first element of the array.\nGets a pointer to the first element of the array.\nAssuming all the elements are initialized, get a mutable …\nAssuming all the elements are initialized, get a slice to …\nTransposes a <code>MaybeUninit&lt;[T; N]&gt;</code> into a <code>[MaybeUninit&lt;T&gt;; N]</code>…\nCreates a new <code>MaybeUninit&lt;T&gt;</code> in an uninitialized state.\nCreate a new array of <code>MaybeUninit&lt;T&gt;</code> items, in an …\nSets the value of the <code>MaybeUninit&lt;T&gt;</code>.\nReturns the additive identity element of <code>Self</code>, <code>0</code>.\nCreates a new <code>MaybeUninit&lt;T&gt;</code> in an uninitialized state, …\nA trait for giving a type a useful default value.\nDerive macro generating an impl of the trait <code>Default</code>.\nContains the error value\nConfiguration for formatting.\nA value-to-value conversion that consumes the input value. …\nContains the success value\nThe type returned by formatter methods.\nReturns the “default value” for a type.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nConverts this type into the (usually inferred) input type.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nUsed to do a cheap reference-to-reference conversion.\n<code>?</code> formatting.\nDerive macro generating an impl of the trait <code>Debug</code>.\nA trait for giving a type a useful default value.\nDerive macro generating an impl of the trait <code>Default</code>.\nTrait for comparisons corresponding to equivalence …\nDerive macro generating an impl of the trait <code>Eq</code>.\nConfiguration for formatting.\nA hashable type.\nDerive macro generating an impl of the trait <code>Hash</code>.\nA trait for hashing an arbitrary stream of bytes.\nA single-threaded reference-counting pointer. ‘Rc’ …\nFlag indicating what form of alignment was requested.\nReturns a reference to the underlying allocator.\nDetermines if the <code>#</code> flag was specified.\nProvides a raw pointer to the data.\nConverts this type into a shared reference of the (usually …\nConverts to <code>Rc&lt;T&gt;</code>.\nConverts to <code>Rc&lt;[T]&gt;</code>.\nReturns the cardinality of this <code>Sequence&lt;T&gt;</code>.\nMakes a clone of the <code>Rc</code> pointer.\nComparison for two <code>Rc</code>s.\nCreates a <code>DebugList</code> builder designed to assist with …\nCreates a <code>DebugMap</code> builder designed to assist with …\nCreates a <code>DebugSet</code> builder designed to assist with …\nCreates a <code>DebugStruct</code> builder designed to assist with …\nCreates a <code>DebugTuple</code> builder designed to assist with …\nDecrements the strong reference count on the <code>Rc&lt;T&gt;</code> …\nDecrements the strong reference count on the <code>Rc&lt;T&gt;</code> …\nReturns the “default value” for a type.\nCreates an empty <code>[T]</code> inside an Rc\nCreates an empty CStr inside an Rc\nCreates an empty str inside an Rc\nCreates a new <code>Rc&lt;T&gt;</code>, with the <code>Default</code> value for <code>T</code>.\nAttempt to downcast the <code>Rc&lt;dyn Any&gt;</code> to a concrete type.\nDowncasts the <code>Rc&lt;dyn Any&gt;</code> to a concrete type.\nCreates a new <code>Weak</code> pointer to this allocation.\nDrops the <code>Rc</code>.\nEquality for two <code>Rc</code>s.\nCharacter used as ‘fill’ whenever there is alignment.\nReturns the hash value for the values written so far.\nFlags for formatting\nFormats the value using the given formatter.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nAllocate a reference-counted slice and move <code>v</code>’s items …\nConverts a reference-counted string slice into a byte …\nConverts a <code>&amp;CStr</code> into a <code>Rc&lt;CStr&gt;</code>, by copying the contents …\nCreate a reference-counted pointer from a clone-on-write …\nAllocate a reference-counted string slice and copy <code>v</code> into …\nMove a boxed object to a new, reference counted, …\nConverts a <code>PathBuf</code> into an Rc&lt;Path&gt; by moving the <code>PathBuf</code> …\nReturns the argument unchanged.\nConverts a generic type <code>T</code> into an <code>Rc&lt;T&gt;</code>\nConverts a <code>CString</code> into an Rc&lt;CStr&gt; by moving the <code>CString</code> …\nCopies the string into a newly allocated Rc&lt;OsStr&gt;.\nConverts an <code>OsString</code> into an Rc&lt;OsStr&gt; by moving the …\nConverts a <code>Path</code> into an <code>Rc</code> by copying the <code>Path</code> data into a …\nConverts a <code>[T; N]</code> into an <code>Rc&lt;[T]&gt;</code>.\nAllocate a reference-counted slice and fill it by cloning <code>v</code>…\nAllocate a reference-counted string slice and copy <code>v</code> into …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nTakes each element in the <code>Iterator</code> and collects it into an …\nConstructs an <code>Rc&lt;T&gt;</code> from a raw pointer.\nConstructs an <code>Rc&lt;T, A&gt;</code> from a raw pointer in the provided …\n‘Greater than or equal to’ comparison for two <code>Rc</code>s.\nReturns a mutable reference into the given <code>Rc</code>, if there are\nReturns a mutable reference into the given <code>Rc</code>, without any …\nGreater-than comparison for two <code>Rc</code>s.\nFeeds this value into the given <code>Hasher</code>.\nFeeds a slice of this type into the given <code>Hasher</code>.\nIncrements the strong reference count on the <code>Rc&lt;T&gt;</code> …\nIncrements the strong reference count on the <code>Rc&lt;T&gt;</code> …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns the inner value, if the <code>Rc</code> has exactly one strong …\nConsumes the <code>Rc</code>, returning the wrapped pointer.\nConsumes the <code>Rc</code>, returning the wrapped pointer and …\n‘Less than or equal to’ comparison for two <code>Rc</code>s.\nLess-than comparison for two <code>Rc</code>s.\nMakes a mutable reference into the given <code>Rc</code>.\nInequality for two <code>Rc</code>s.\nConstructs a new <code>Rc&lt;T&gt;</code>.\nConstructs a new <code>Rc&lt;T&gt;</code> while giving you a <code>Weak&lt;T&gt;</code> to the …\nConstructs a new <code>Rc</code> in the provided allocator.\nConstructs a new <code>Rc</code> with uninitialized contents.\nConstructs a new <code>Rc</code> with uninitialized contents in the …\nConstructs a new reference-counted slice with …\nConstructs a new reference-counted slice with …\nConstructs a new <code>Rc</code> with uninitialized contents, with the …\nConstructs a new <code>Rc</code> with uninitialized contents, with the …\nConstructs a new reference-counted slice with …\nConstructs a new reference-counted slice with …\nThis function takes a string slice and emits it to the …\nPerforms the correct padding for an integer which has …\nPartial comparison for two <code>Rc</code>s.\nConstructs a new <code>Pin&lt;Rc&lt;T&gt;&gt;</code>. If <code>T</code> does not implement <code>Unpin</code>…\nConstructs a new <code>Pin&lt;Rc&lt;T&gt;&gt;</code> in the provided allocator. If <code>T</code>…\nOptionally specified precision for numeric types. …\nReturns <code>true</code> if the two <code>Rc</code>s point to the same allocation …\nDetermines if the <code>0</code> flag was specified.\nDetermines if the <code>-</code> flag was specified.\nDetermines if the <code>+</code> flag was specified.\nGets the number of strong (<code>Rc</code>) pointers to this allocation.\nConstructs a new <code>Rc&lt;T&gt;</code>, returning an error if the …\nConstructs a new <code>Rc&lt;T&gt;</code> in the provided allocator, …\nConstructs a new <code>Rc</code> with uninitialized contents, returning …\nConstructs a new <code>Rc</code> with uninitialized contents, in the …\nConstructs a new <code>Rc</code> with uninitialized contents, with the …\nConstructs a new <code>Rc</code> with uninitialized contents, with the …\nReturns the inner value, if the <code>Rc</code> has exactly one strong …\nIf we have the only reference to <code>T</code> then unwrap it. …\nGets the number of <code>Weak</code> pointers to this allocation.\nOptionally specified integer width that the output should …\nWrites some data into this <code>Hasher</code>.\nWrites some formatted information into this instance.\nWrites a single <code>i128</code> into this hasher.\nWrites a single <code>i16</code> into this hasher.\nWrites a single <code>i32</code> into this hasher.\nWrites a single <code>i64</code> into this hasher.\nWrites a single <code>i8</code> into this hasher.\nWrites a single <code>isize</code> into this hasher.\nWrites a length prefix into this hasher, as part of being …\nWrites some data to the underlying buffer contained within …\nWrites a single <code>str</code> into this hasher.\nWrites a single <code>u128</code> into this hasher.\nWrites a single <code>u16</code> into this hasher.\nWrites a single <code>u32</code> into this hasher.\nWrites a single <code>u64</code> into this hasher.\nWrites a single <code>u8</code> into this hasher.\nWrites a single <code>usize</code> into this hasher.\nA service that supports the operation of getting things.\nReturns the argument unchanged.\nCreates a new client from the service <code>Config</code>.\nConstructs a fluent builder for the <code>GetThing</code> operation.\nCalls <code>U::from(self)</code>.\nWraps up an arbitrary Rust Error value as a Dafny Error\nWraps up an arbitrary Rust Error value as a Dafny Result&lt;…\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nA boxed error that is <code>Send</code> and <code>Sync</code>.\nAn error occurred attempting to build an <code>Operation</code> from an …\nError from the underlying Connector\nThe request failed during construction. It was not …\nThe request failed during dispatch. An HTTP response was …\nProvides a <code>Display</code> impl for an <code>Error</code> that outputs the full …\nGeneric Error type\nTrait to retrieve error metadata from a result\nA response was received but it was not parseable according …\nError type returned by the client.\nAn error response was received from the service\nThe request failed due to a timeout. The request MAY have …\nReturns the optional error kind associated with an …\nCreates an <code>Error</code> builder.\nReturns the error code if it’s available.\nReturns the error code.\nReturns metadata about the connection\nReturns additional information about the error if it’s …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nConverts an <code>Error</code> into a builder.\nGrants ownership of this error’s source.\nConstruct a build error for an invalid field\nConstruct a <code>ConnectorError</code> from an IO related error (e.g. …\nReturns true if the error is an IO error\nReturns true if the error is an unclassified error.\nReturns true if the error is an timeout error\nReturns true if the error is a user-caused error (e.g., …\nReturns the error message, if there is one.\nReturns the error message.\nReturns error metadata, which includes the error code, …\nConstruct a build error for a missing field\nSet the connection status on this error to report that a …\nConstruct a build error from another underlying error\nConstruct a <code>ConnectorError</code> from an different unclassified …\nConstruct a <code>ConnectorError</code> from an error caused by a …\nConstruct a <code>ConnectorError</code> from an error caused by the …\nInclude connection information along with this error\nTypes for the <code>GetThing</code> operation.\nTypes for the <code>SetWidgetName</code> operation.\nOrchestration and serialization glue logic for <code>GetThing</code>.\nA service that supports the operation of getting things.\nA service that supports the operation of getting things.\nCreates a new builder-style object to manufacture …\nCreates a new builder-style object to manufacture …\nBuilders\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe name of the thing to get, obviously.\nThe name of the thing to get, obviously.\nCreates a new <code>GetThing</code>\nThe thing that you just got.\nThe thing that you just got.\nFluent builder constructing a request to <code>GetThing</code>.\nA builder for <code>GetThingInput</code>.\nA builder for <code>GetThingOutput</code>.\nAccess the GetThing as a reference.\nConsumes the builder and constructs a <code>GetThingOutput</code>.\nConsumes the builder and constructs a <code>GetThingInput</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nThe name of the thing to get, obviously.\nThe name of the thing to get, obviously.\nThe thing that you just got.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe name of the thing to get, obviously.\nThe name of the thing to get, obviously.\nSends the request and returns the response.\nSends a request with this input using the given client.\nThe name of the thing to get, obviously.\nThe name of the thing to get, obviously.\nThe thing that you just got.\nThe thing that you just got.\nOrchestration and serialization glue logic for …\nA service that supports the operation of getting things.\nA service that supports the operation of getting things.\nCreates a new builder-style object to manufacture <code>Unit</code>.\nCreates a new builder-style object to manufacture …\nBuilders\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates a new <code>SetWidgetName</code>\nFluent builder constructing a request to <code>SetWidgetName</code>.\nA builder for <code>SetWidgetNameInput</code>.\nA builder for <code>Unit</code>.\nAccess the SetWidgetName as a reference.\nConsumes the builder and constructs a <code>Unit</code>.\nConsumes the builder and constructs a <code>SetWidgetNameInput</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nSends the request and returns the response.\nSends a request with this input using the given client.\nA trait to emulate dynamic typing.\nA single-threaded reference-counting pointer. ‘Rc’ …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nGets the <code>TypeId</code> of <code>self</code>.\nA trait to emulate dynamic typing.\nUsed to do a cheap reference-to-reference conversion.\n<code>?</code> formatting.\nDerive macro generating an impl of the trait <code>Debug</code>.\nA trait for giving a type a useful default value.\nDerive macro generating an impl of the trait <code>Default</code>.\nTrait for comparisons corresponding to equivalence …\nDerive macro generating an impl of the trait <code>Eq</code>.\nConfiguration for formatting.\nA hashable type.\nDerive macro generating an impl of the trait <code>Hash</code>.\nA trait for hashing an arbitrary stream of bytes.\nA single-threaded reference-counting pointer. ‘Rc’ …\nConverts this type into a shared reference of the (usually …\nReturns the “default value” for a type.\nReturns the hash value for the values written so far.\nFormats the value using the given formatter.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nFeeds this value into the given <code>Hasher</code>.\nFeeds a slice of this type into the given <code>Hasher</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nGets the <code>TypeId</code> of <code>self</code>.\nWrites some data into this <code>Hasher</code>.\nWrites a single <code>i128</code> into this hasher.\nWrites a single <code>i16</code> into this hasher.\nWrites a single <code>i32</code> into this hasher.\nWrites a single <code>i64</code> into this hasher.\nWrites a single <code>i8</code> into this hasher.\nWrites a single <code>isize</code> into this hasher.\nWrites a length prefix into this hasher, as part of being …\nWrites a single <code>str</code> into this hasher.\nWrites a single <code>u128</code> into this hasher.\nWrites a single <code>u16</code> into this hasher.\nWrites a single <code>u32</code> into this hasher.\nWrites a single <code>u64</code> into this hasher.\nWrites a single <code>u8</code> into this hasher.\nWrites a single <code>usize</code> into this hasher.\nInputs for getting a thing.\nEither kind of thing.\nA thing that you can get from the service.\nThe <code>Unknown</code> variant represents cases where new union …\nTypes of widgets you can get.\nTries to convert the enum instance into <code>Thing</code>, extracting …\nTries to convert the enum instance into <code>Widget</code>, extracting …\nCreates a new builder-style object to manufacture …\nCreates a new builder-style object to manufacture …\nCreates a new builder-style object to manufacture …\nCreates a new builder-style object to manufacture <code>Thing</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns true if this is a <code>Thing</code>.\nReturns true if the enum instance is the <code>Unknown</code> variant.\nReturns true if this is a <code>Widget</code>.\nThe name of the thing to get, obviously.\nThe name of the thing.\nThe name of the thing to get, obviously.\nThe name of the thing.\nTypes for the <code>SimpleDocumentationConfig</code>\nThe thing that you just got.\nThe thing that you just got.\nA builder for <code>GetThingInput</code>.\nA builder for <code>GetThingOutput</code>.\nA builder for <code>SetWidgetNameInput</code>.\nA builder for <code>Thing</code>.\nConsumes the builder and constructs a <code>GetThingInput</code>.\nConsumes the builder and constructs a <code>GetThingOutput</code>.\nConsumes the builder and constructs a <code>SetWidgetNameInput</code>.\nConsumes the builder and constructs a <code>Thing</code>.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nThe name of the thing to get, obviously.\nThe name of the thing.\nThe thing that you just got.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nThe name of the thing to get, obviously.\nThe name of the thing.\nThe name of the thing to get, obviously.\nThe name of the thing.\nThe thing that you just got.\nThe thing that you just got.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nFancy configuration things to make getting things even …\nA builder for <code>SimpleDocumentationConfig</code>.\nConsumes the builder and constructs a …\nCreates a new builder-style object to manufacture …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nA different kind of thing you can get. Also exercising …\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nConstructs a fluent builder for the <code>SetWidgetName</code> …")