extern crate simple_constraints;

/// Smoke tests for constraint validation when calling in from Rust code.
mod simple_constraints_test {
    use simple_constraints::*;

    use std::collections::HashMap;

    fn client() -> Client {
        let config = SimpleConstraintsConfig::builder()
            .required_string("test string")
            .build()
            .expect("config");
        client::Client::from_conf(config).expect("client")
    }

    #[test]
    fn test_config_missing_field() {
        let config = SimpleConstraintsConfig::builder()
            .build()
            .expect("config");
        let error = client::Client::from_conf(config).err().expect("err");
        assert!(matches!(
            error,
            simple_constraints::types::error::Error::ValidationError(..)
        ));
        assert!(error.to_string().contains("required_string"));
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

    #[tokio::test]
    async fn test_good_list_with_constraint() {
        let vec = vec!["1".to_string(), "123".to_string(), "1234567890".to_string()];
        let result = client().get_constraints()
            .list_with_constraint(vec)
            .send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_bad_list_with_constraint() {
        let vec = vec!["".to_string(), "this string is too long".to_string()];
        let result = client().get_constraints()
            .list_with_constraint(vec)
            .send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("member"));
    }

    #[tokio::test]
    async fn test_good_map_with_constraint() {
        let mut map = HashMap::new();
        map.insert("foo".to_string(), "bar".to_string());

        let result = client().get_constraints()
            .map_with_constraint(map)
            .send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_bad_map_with_constraint() {
        let mut map = HashMap::new();
        map.insert("this key is too long".to_string(), "bar".to_string());

        let result = client().get_constraints()
            .map_with_constraint(map)
            .send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("key"));

        let mut map = HashMap::new();
        map.insert("foo".to_string(), "this value is too long".to_string());

        let result = client().get_constraints()
            .map_with_constraint(map)
            .send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("value"));
    }

    #[tokio::test]
    async fn test_good_union_with_constraint() {
        let union_val = types::UnionWithConstraint::IntegerValue(1);
        let result = client().get_constraints()
            .union_with_constraint(union_val)
            .send().await;
        assert!(result.is_ok());

        let union_val = types::UnionWithConstraint::StringValue("foo".to_string());
        let result = client().get_constraints()
            .union_with_constraint(union_val)
            .send().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_bad_union_with_constraint() {
        let union_val = types::UnionWithConstraint::IntegerValue(100);
        let result = client().get_constraints()
            .union_with_constraint(union_val)
            .send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("integer_value"));

        let union_val = types::UnionWithConstraint::StringValue("this string is too long".to_string());
        let result = client().get_constraints()
            .union_with_constraint(union_val)
            .send().await;
        let message = result.err().expect("error").to_string();
        assert!(message.contains("string_value"));
    }
}
