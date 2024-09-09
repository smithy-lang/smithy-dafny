pub use ::aws_smithy_runtime_api::box_error::BoxError;

/// Error type returned by the client.
pub type SdkError<E, R = ::aws_smithy_runtime_api::client::orchestrator::HttpResponse> =
    ::aws_smithy_runtime_api::client::result::SdkError<E, R>;
pub use ::aws_smithy_runtime_api::client::result::ConnectorError;
pub use ::aws_smithy_types::error::operation::BuildError;

pub use ::aws_smithy_types::error::display::DisplayErrorContext;
pub use ::aws_smithy_types::error::metadata::ErrorMetadata;
pub use ::aws_smithy_types::error::metadata::ProvideErrorMetadata;
