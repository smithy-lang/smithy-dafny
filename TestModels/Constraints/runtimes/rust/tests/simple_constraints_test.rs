extern crate simple_constraints;

/// Smoke tests for constraint validation when calling in from Rust code.
mod simple_constraints_test {
    use simple_constraints::*;

    fn client() -> Client {
        let config = SimpleConstraintsConfig::builder().build().expect("config");
        client::Client::from_conf(config).expect("client")
    }

    #[tokio::test]
    async fn test_empty_input() {
        let result = client().get_constraints().send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_short_string() {
        let result = client().get_constraints().my_string("").send().await;
        let error = result.err().expect("error");
        assert!(matches!(
            error,
            simple_constraints::types::error::Error::ValidationError(..)
        ));
        assert!(error.to_string().contains("my_string"));

        use std::error::Error;
        let source_message = error.source().expect("source").to_string();
        assert!(source_message.contains("my_string"));
    }

    #[tokio::test]
    async fn test_good_string() {
        let result = client().get_constraints().my_string("good").send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_long_string() {
        let result = client()
            .get_constraints()
            .my_string("too many characters")
            .send()
            .await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("my_string"));
    }

    #[tokio::test]
    async fn test_small_int() {
        let result = client().get_constraints().one_to_ten(0).send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("one_to_ten"));
    }

    #[tokio::test]
    async fn test_good_int() {
        let result = client().get_constraints().one_to_ten(5).send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_big_int() {
        let result = client().get_constraints().one_to_ten(99).send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("one_to_ten"));
    }
}
