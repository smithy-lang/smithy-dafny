searchState.loadedDescShard("aws_smithy_async", 0, "Future utilities and runtime-agnostic abstractions for …\nGiven an <code>Instant</code> and a <code>Duration</code>, assert time elapsed since …\nUseful runtime-agnostic future implementations.\nAsync runtime agnostic traits and implementations.\nTime source abstraction to support WASM and testing\nA boxed future that outputs a <code>Result&lt;T, E&gt;</code>.\nProvides the <code>Never</code> future that never completes.\nProvides the <code>NowOrLater</code> future with an explicit <code>Now</code> variant\nProvides types to support stream-like operations for …\nRendezvous channel implementation\nProvides the <code>Timeout</code> future for adding a timeout to …\nFuture that never completes.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCreate a new <code>Never</code> future that never resolves\nBoxed future type alias\nFuture with an explicit <code>Now</code> variant\nZero sized type for using NowOrLater when no future …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates a future that will resolve when <code>future</code> resolves\nCreates a future that immediately resolves to <code>value</code>\nStream specifically made to support paginators.\nUtility wrapper to flatten paginated results\nModule to extend the functionality of types in …\nConsumes this stream and gathers elements into a …\nProduces a new <code>PaginationStream</code> by mapping this stream …\nModule to define utility to drive a stream with an async …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates a <code>PaginationStream</code> from the given <code>FnStream</code>.\nCreates a <code>TryFlatMap</code> that wraps the input.\nConsumes and returns the next <code>Item</code> from this stream.\nPoll an item from the stream\nConvenience method for <code>.collect::&lt;Result&lt;Vec&lt;_&gt;, _&gt;()</code>.\nYields the next item in the stream or returns an error if …\nThe closure is passed a reference to a <code>Sender</code> which acts …\nConsumes this stream and gathers elements into a …\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCreates a new function based stream driven by <code>generator</code>.\nConsumes and returns the next <code>Item</code> from this stream.\nConvenience method for <code>.collect::&lt;Result&lt;Vec&lt;_&gt;, _&gt;()</code>.\nYields the next item in the stream or returns an error if …\nReceiver half of the rendezvous channel\nSender-half of a channel\nCreate a new rendezvous channel\nErrors for rendezvous channel\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nPolls to receive an item from the channel\nSend <code>item</code> into the channel waiting until there is matching …\nError when crate::future::rendezvous::Sender fails to send …\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nError returned when <code>Timeout</code> times out\nTimeout Future\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreate a new future that will race <code>value</code> and <code>sleep</code>.\nProvides an <code>AsyncSleep</code> trait that returns a future that …\nAsync trait with a <code>sleep</code> function.\nWrapper type for sharable <code>AsyncSleep</code>\nFuture returned by <code>AsyncSleep</code>.\nReturns a default sleep implementation based on the …\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreate a new <code>Sleep</code> future\nCreate a new <code>SharedAsyncSleep</code> from <code>AsyncSleep</code>\nReturns a future that sleeps for the given <code>duration</code> of …\nTime source structure used inside SDK\nTime source that always returns the same time\nTime source that delegates to <code>SystemTime::now</code>\nTrait with a <code>now()</code> function returning the current time\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCreates a new static time source from the provided number …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCreates a new SystemTimeSource\nCreates a new static time source that always returns the …\nCreates a new shared time source\nReturns the current time\nReturns the current time")