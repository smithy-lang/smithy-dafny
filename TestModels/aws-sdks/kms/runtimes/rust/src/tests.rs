async fn async_fn() {
    crate::client::escape_to_async(tokio::time::sleep(std::time::Duration::from_millis(100)));
}

fn sync_fn() {
    async_fn();
}

#[test]
fn plain_test() {
    sync_fn();
}

#[tokio::test]
async fn tokio_test() {
    sync_fn();
}

#[tokio::test(flavor = "multi_thread")]
async fn tokio_test_multi() {
    sync_fn();
}

#[tokio::test(flavor = "current_thread")]
async fn tokio_test_current() {
    sync_fn();
}
