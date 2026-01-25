// Unit test to verify pagination fix for Letta SDK compatibility
//
// Tests the `?after=<id>` parameter for cursor-based pagination

use kelpie_core::TokioRuntime;
use kelpie_server::models::{AgentType, CreateAgentRequest};
use kelpie_server::state::AppState;

#[tokio::test]
async fn test_list_agents_pagination_with_after_cursor() {
    let state = AppState::new(TokioRuntime);

    // Create 5 agents
    for i in 0..5 {
        let request = CreateAgentRequest {
            name: format!("agent_{}", i),
            agent_type: AgentType::MemgptAgent,
            ..Default::default()
        };

        state.create_agent_async(request).await.unwrap();
    }

    // List all agents (should return 5)
    let (all_agents, _cursor) = state.list_agents_async(10, None, None).await.unwrap();
    assert_eq!(all_agents.len(), 5, "Should return all 5 agents");

    // Use the FIRST agent from the sorted list (not first created)
    // This ensures we're testing pagination in the middle of the list
    let first_sorted_id = &all_agents[0].id;

    // List after first sorted agent (should return remaining 4)
    let (after_agents, _cursor) = state
        .list_agents_async(10, Some(first_sorted_id), None)
        .await
        .unwrap();

    assert_eq!(
        after_agents.len(),
        4,
        "Should return 4 agents after first sorted agent"
    );

    // Verify the first agent is NOT in the results (cursor is excluded)
    assert!(
        !after_agents.iter().any(|a| a.id == *first_sorted_id),
        "Cursor agent should not be in results (cursor should be excluded)"
    );

    // List after middle agent (use 3rd agent from sorted list)
    let middle_id = &all_agents[2].id;
    let (middle_agents, _cursor) = state
        .list_agents_async(10, Some(middle_id), None)
        .await
        .unwrap();

    assert_eq!(
        middle_agents.len(),
        2,
        "Should return 2 agents after middle cursor (agents 3 and 4)"
    );

    // List after last agent (should return 0)
    let last_id = &all_agents[all_agents.len() - 1].id;
    let (end_agents, cursor) = state
        .list_agents_async(10, Some(last_id), None)
        .await
        .unwrap();

    assert_eq!(end_agents.len(), 0, "Should return 0 agents after last");
    assert!(cursor.is_none(), "Cursor should be None at end of list");
}

#[tokio::test]
async fn test_list_agents_pagination_with_limit() {
    let state = AppState::new(TokioRuntime);

    // Create 10 agents
    for i in 0..10 {
        let request = CreateAgentRequest {
            name: format!("agent_{}", i),
            agent_type: AgentType::MemgptAgent,
            ..Default::default()
        };

        state.create_agent_async(request).await.unwrap();
    }

    // List with limit=3 (should return 3 and next cursor)
    let (page1, cursor1) = state.list_agents_async(3, None, None).await.unwrap();

    assert_eq!(page1.len(), 3, "First page should have 3 agents");
    assert!(cursor1.is_some(), "Should have next cursor");

    // List next page using cursor
    let (page2, cursor2) = state
        .list_agents_async(3, cursor1.as_deref(), None)
        .await
        .unwrap();

    assert_eq!(page2.len(), 3, "Second page should have 3 agents");
    assert!(cursor2.is_some(), "Should have next cursor");

    // Verify no overlap between pages
    for agent in &page2 {
        assert!(
            !page1.iter().any(|a| a.id == agent.id),
            "Pages should not overlap"
        );
    }
}
