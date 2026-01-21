use sample_crate::*;

#[test]
fn test_user_creation() {
    let user = create_user(42, "Bob".to_string());
    assert_eq!(user.id, 42);
}

#[tokio::test]
async fn test_async_fetch() {
    let user = fetch_user(99).await;
    assert!(user.is_some());
}

#[test]
fn test_status_enum() {
    let status = Status::Active;
    matches!(status, Status::Active);
}
