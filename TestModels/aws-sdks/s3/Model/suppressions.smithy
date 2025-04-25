$version: "2"

namespace doesnt.matter

// Streaming isn't yet supported,
// but we still want to test against the rest of the S3 model.
apply com.amazonaws.s3#StreamingBlob @suppress(["UnsupportedFeatures"])