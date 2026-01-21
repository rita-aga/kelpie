/// Sample public struct for testing
#[derive(Debug, Clone)]
pub struct User {
    pub id: u64,
    pub name: String,
}

/// Sample public function
pub fn create_user(id: u64, name: String) -> User {
    User { id, name }
}

/// Sample async function
pub async fn fetch_user(id: u64) -> Option<User> {
    // Simulated fetch
    Some(User {
        id,
        name: "Test User".to_string(),
    })
}

/// Sample trait
pub trait Repository {
    fn save(&self, user: &User);
    fn load(&self, id: u64) -> Option<User>;
}

/// Sample enum
#[derive(Debug)]
pub enum Status {
    Active,
    Inactive,
    Pending,
}

// Private helper function (should still be indexed)
fn validate_name(name: &str) -> bool {
    !name.is_empty() && name.len() < 100
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_user() {
        let user = create_user(1, "Alice".to_string());
        assert_eq!(user.id, 1);
        assert_eq!(user.name, "Alice");
    }

    #[test]
    fn test_validate_name() {
        assert!(validate_name("Alice"));
        assert!(!validate_name(""));
    }

    #[tokio::test]
    async fn test_fetch_user() {
        let user = fetch_user(1).await;
        assert!(user.is_some());
    }
}
