pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationOutputName:L::$pascalCaseOperationOutputName:LBuilder;

pub use crate::operation::$snakeCaseOperationName:L::_$snakeCaseOperationInputName:L::$pascalCaseOperationInputName:LBuilder;

impl $pascalCaseOperationInputName:LBuilder {
    /// Sends a request with this input using the given client.
    pub async fn send_with(
        self,
        client: &crate::Client,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        crate::types::error::Error,
    > {
        let mut fluent_builder = client.$snakeCaseOperationName:L();
        fluent_builder.inner = self;
        fluent_builder.send().await
    }
}
/// Fluent builder constructing a request to `$pascalCaseOperationName:L`.
///
#[derive(::std::clone::Clone, ::std::fmt::Debug)]
pub struct $pascalCaseOperationName:LFluentBuilder {
    client: crate::client::Client,
    pub(crate) inner: crate::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationInputName:LBuilder,
}
impl $pascalCaseOperationName:LFluentBuilder {
    /// Creates a new `$pascalCaseOperationName:L`.
    pub(crate) fn new(client: crate::client::Client) -> Self {
        Self {
            client,
            inner: ::std::default::Default::default(),
        }
    }
    /// Access the $pascalCaseOperationName:L as a reference.
    pub fn as_input(&self) -> &crate::operation::$snakeCaseOperationName:L::builders::$pascalCaseOperationInputName:LBuilder {
        &self.inner
    }
    /// Sends the request and returns the response.
    pub async fn send(
        self,
    ) -> ::std::result::Result<
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L,
        crate::types::error::Error,
    > {
        let input = self.inner.build()?;
        crate::operation::$snakeCaseOperationName:L::$pascalCaseOperationName:L::send(&self.client, input).await
    }

    $accessors:L
}