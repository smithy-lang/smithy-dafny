# Streaming

This project will implement the smithy trait [streaming](https://smithy.io/2.0/spec/streaming.html#smithy-api-streaming-trait) and the associated operations in `dafny`.

## Status

This project only currently works on Python: the Dafny code generation
has been updated to support `@streaming` on blob shapes,
but only Python includes shim adaptors between the Dafny types
and the types used for Smithy-generated interfaces.
