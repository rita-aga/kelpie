#!/usr/bin/env python3
"""
Test Letta SDK compatibility with Kelpie server.

This script acts as a real user migrating from Letta to Kelpie.
It uses the official letta-client SDK and documents what works.

Usage:
    1. Start Kelpie: ANTHROPIC_API_KEY=... cargo run -p kelpie-server
    2. Run: python test_letta_sdk.py

Requirements:
    pip install letta-client requests
"""

import sys
import time
import json
from dataclasses import dataclass
from typing import Optional, List, Any

# Try to import letta-client
try:
    from letta_client import Letta
    LETTA_SDK_AVAILABLE = True
except ImportError:
    LETTA_SDK_AVAILABLE = False
    print("⚠️  letta-client not installed. Install with: pip install letta-client")
    print("   Falling back to raw HTTP requests for testing.\n")

import requests

KELPIE_URL = "http://localhost:8283"


@dataclass
class TestResult:
    name: str
    passed: bool
    message: str
    details: Optional[str] = None


class LettaMigrationTester:
    """Test Letta SDK compatibility with Kelpie."""
    
    def __init__(self, base_url: str = KELPIE_URL):
        self.base_url = base_url
        self.results: List[TestResult] = []
        self.agent_id: Optional[str] = None
        
        if LETTA_SDK_AVAILABLE:
            try:
                # Initialize Letta client pointing to Kelpie
                # The Letta SDK uses api_key and environment parameters
                self.client = Letta(
                    base_url=base_url,
                    environment="local",  # Skip cloud auth
                )
                print(f"✅ Letta SDK initialized successfully")
            except Exception as e:
                print(f"⚠️  Failed to initialize Letta client: {e}")
                self.client = None
        else:
            self.client = None
    
    def log_result(self, name: str, passed: bool, message: str, details: str = None):
        result = TestResult(name, passed, message, details)
        self.results.append(result)
        status = "✅" if passed else "❌"
        print(f"{status} {name}: {message}")
        if details and not passed:
            print(f"   Details: {details}")
    
    def test_server_health(self) -> bool:
        """Test 1: Check if Kelpie server is running."""
        try:
            resp = requests.get(f"{self.base_url}/health", timeout=5)
            if resp.status_code == 200:
                data = resp.json()
                self.log_result(
                    "Server Health",
                    True,
                    f"Server running (version: {data.get('version', 'unknown')})"
                )
                return True
            else:
                self.log_result("Server Health", False, f"HTTP {resp.status_code}")
                return False
        except requests.exceptions.ConnectionError:
            self.log_result(
                "Server Health",
                False,
                "Connection refused - is Kelpie running?",
                "Start with: cargo run -p kelpie-server"
            )
            return False
        except Exception as e:
            self.log_result("Server Health", False, str(e))
            return False
    
    def test_create_agent_sdk(self) -> bool:
        """Test 2a: Create agent using Letta SDK (modern API)."""
        if not self.client:
            self.log_result(
                "Create Agent (SDK)",
                False,
                "Letta SDK not available",
                "pip install letta-client"
            )
            return False
        
        try:
            # Modern Letta SDK uses memory_blocks with CreateBlockParam format
            agent = self.client.agents.create(
                name="kelpie-test-agent",
                memory_blocks=[
                    {"label": "persona", "value": "You are a helpful assistant running on Kelpie."},
                    {"label": "human", "value": "The user is testing Letta SDK compatibility."}
                ]
            )
            
            self.agent_id = agent.id
            self.log_result(
                "Create Agent (SDK)",
                True,
                f"Created agent: {agent.id[:8]}..."
            )
            return True
            
        except Exception as e:
            error_msg = str(e)
            # Check if it's a specific API incompatibility
            if "unexpected keyword argument" in error_msg:
                self.log_result(
                    "Create Agent (SDK)",
                    False,
                    "API mismatch - SDK expects different parameters",
                    error_msg[:200]
                )
            elif "422" in error_msg or "validation" in error_msg.lower():
                self.log_result(
                    "Create Agent (SDK)",
                    False,
                    "Validation error - request format mismatch",
                    error_msg[:200]
                )
            else:
                self.log_result(
                    "Create Agent (SDK)",
                    False,
                    f"Failed: {type(e).__name__}",
                    error_msg[:200]
                )
            return False
    
    def test_create_agent_http(self) -> bool:
        """Test 2b: Create agent using raw HTTP (fallback)."""
        try:
            resp = requests.post(
                f"{self.base_url}/v1/agents",
                json={
                    "name": "kelpie-test-agent-http",
                    "memory_blocks": [
                        {"label": "persona", "value": "You are a helpful assistant."},
                        {"label": "human", "value": "Testing Kelpie compatibility."}
                    ]
                },
                timeout=10
            )
            
            if resp.status_code in (200, 201):
                data = resp.json()
                self.agent_id = data.get("id")
                self.log_result(
                    "Create Agent (HTTP)",
                    True,
                    f"Created agent: {self.agent_id[:8] if self.agent_id else 'unknown'}..."
                )
                return True
            else:
                self.log_result(
                    "Create Agent (HTTP)",
                    False,
                    f"HTTP {resp.status_code}",
                    resp.text[:200]
                )
                return False
                
        except Exception as e:
            self.log_result("Create Agent (HTTP)", False, str(e))
            return False
    
    def test_list_agents_sdk(self) -> bool:
        """Test 3a: List agents using Letta SDK."""
        if not self.client:
            return self.test_list_agents_http()
        
        try:
            # Modern SDK returns SyncArrayPage, need to iterate or convert
            agents_page = self.client.agents.list()
            agents = list(agents_page)  # Convert page to list
            
            # Check if our agent is in the list
            found = any(a.id == self.agent_id for a in agents) if self.agent_id else len(agents) > 0
            
            self.log_result(
                "List Agents (SDK)",
                True,
                f"Found {len(agents)} agents"
            )
            return True
            
        except Exception as e:
            self.log_result(
                "List Agents (SDK)",
                False,
                f"Failed: {type(e).__name__}",
                str(e)[:200]
            )
            return self.test_list_agents_http()
    
    def test_list_agents_http(self) -> bool:
        """Test 3b: List agents using HTTP."""
        try:
            resp = requests.get(f"{self.base_url}/v1/agents", timeout=10)
            
            if resp.status_code == 200:
                agents = resp.json()
                count = len(agents) if isinstance(agents, list) else "unknown"
                self.log_result(
                    "List Agents (HTTP)",
                    True,
                    f"Found {count} agents"
                )
                return True
            else:
                self.log_result("List Agents (HTTP)", False, f"HTTP {resp.status_code}")
                return False
                
        except Exception as e:
            self.log_result("List Agents (HTTP)", False, str(e))
            return False
    
    def test_get_agent_sdk(self) -> bool:
        """Test 4a: Get agent details using Letta SDK."""
        if not self.client or not self.agent_id:
            return self.test_get_agent_http()
        
        try:
            agent = self.client.agents.retrieve(self.agent_id)
            
            self.log_result(
                "Get Agent (SDK)",
                True,
                f"Agent name: {agent.name}"
            )
            return True
            
        except Exception as e:
            self.log_result(
                "Get Agent (SDK)",
                False,
                f"Failed: {type(e).__name__}",
                str(e)[:200]
            )
            return self.test_get_agent_http()
    
    def test_get_agent_http(self) -> bool:
        """Test 4b: Get agent using HTTP."""
        if not self.agent_id:
            self.log_result("Get Agent (HTTP)", False, "No agent ID available")
            return False
        
        try:
            resp = requests.get(f"{self.base_url}/v1/agents/{self.agent_id}", timeout=10)
            
            if resp.status_code == 200:
                agent = resp.json()
                self.log_result(
                    "Get Agent (HTTP)",
                    True,
                    f"Agent name: {agent.get('name', 'unknown')}"
                )
                return True
            else:
                self.log_result("Get Agent (HTTP)", False, f"HTTP {resp.status_code}")
                return False
                
        except Exception as e:
            self.log_result("Get Agent (HTTP)", False, str(e))
            return False
    
    def test_get_memory_blocks_sdk(self) -> bool:
        """Test 5a: Get memory blocks using Letta SDK."""
        if not self.client or not self.agent_id:
            return self.test_get_memory_blocks_http()
        
        try:
            # Modern SDK might have blocks as a sub-resource
            # Try agent.blocks or client.agents.blocks.list(agent_id)
            if hasattr(self.client.agents, 'blocks'):
                blocks = list(self.client.agents.blocks.list(agent_id=self.agent_id))
                labels = [b.label if hasattr(b, 'label') else str(b) for b in blocks[:3]]
                self.log_result(
                    "Get Memory Blocks (SDK)",
                    True,
                    f"Found {len(blocks)} blocks: {labels}"
                )
                return True
            else:
                # Fall back to HTTP
                return self.test_get_memory_blocks_http()
            
        except Exception as e:
            self.log_result(
                "Get Memory Blocks (SDK)",
                False,
                f"Failed: {type(e).__name__}",
                str(e)[:200]
            )
            return self.test_get_memory_blocks_http()
    
    def test_get_memory_blocks_http(self) -> bool:
        """Test 5b: Get memory blocks using HTTP."""
        if not self.agent_id:
            self.log_result("Get Memory Blocks (HTTP)", False, "No agent ID available")
            return False
        
        try:
            resp = requests.get(
                f"{self.base_url}/v1/agents/{self.agent_id}/blocks",
                timeout=10
            )
            
            if resp.status_code == 200:
                blocks = resp.json()
                if isinstance(blocks, list):
                    labels = [b.get('label', 'unknown') for b in blocks]
                    self.log_result(
                        "Get Memory Blocks (HTTP)",
                        True,
                        f"Blocks: {labels}"
                    )
                else:
                    self.log_result(
                        "Get Memory Blocks (HTTP)",
                        True,
                        f"Blocks response type: {type(blocks).__name__}"
                    )
                return True
            else:
                self.log_result(
                    "Get Memory Blocks (HTTP)",
                    False,
                    f"HTTP {resp.status_code}",
                    resp.text[:200]
                )
                return False
                
        except Exception as e:
            self.log_result("Get Memory Blocks (HTTP)", False, str(e))
            return False
    
    def test_update_memory_block(self) -> bool:
        """Test 6: Update memory block."""
        if not self.agent_id:
            self.log_result("Update Memory Block", False, "No agent ID available")
            return False
        
        # Try multiple paths that Kelpie might support
        paths_to_try = [
            # Letta's path (label-based)
            f"/v1/agents/{self.agent_id}/blocks/human",
            # Kelpie's explicit path
            f"/v1/agents/{self.agent_id}/core-memory/blocks/human",
        ]
        
        for path in paths_to_try:
            try:
                resp = requests.patch(
                    f"{self.base_url}{path}",
                    json={"value": "The user has successfully tested memory updates!"},
                    timeout=10
                )
                
                if resp.status_code == 200:
                    path_type = "Letta" if "/blocks/human" == path.split(self.agent_id)[1] else "Kelpie"
                    self.log_result(
                        "Update Memory Block",
                        True,
                        f"Updated via {path_type} path"
                    )
                    return True
            except Exception:
                continue
        
        self.log_result(
            "Update Memory Block",
            False,
            "Neither Letta nor Kelpie path worked"
        )
        return False
    
    def test_list_tools(self) -> bool:
        """Test 7: List available tools."""
        try:
            resp = requests.get(f"{self.base_url}/v1/tools", timeout=10)
            
            if resp.status_code == 200:
                tools = resp.json()
                if isinstance(tools, list):
                    tool_names = [t.get('name', 'unknown') for t in tools[:5]]
                    self.log_result(
                        "List Tools",
                        True,
                        f"Found {len(tools)} tools: {tool_names}..."
                    )
                elif isinstance(tools, dict):
                    # Kelpie might return tools in a different format
                    self.log_result(
                        "List Tools",
                        True,
                        f"Tools returned as dict with keys: {list(tools.keys())[:5]}"
                    )
                else:
                    self.log_result(
                        "List Tools",
                        True,
                        f"Tools response: {type(tools).__name__}"
                    )
                return True
            else:
                self.log_result("List Tools", False, f"HTTP {resp.status_code}")
                return False
                
        except Exception as e:
            self.log_result("List Tools", False, str(e))
            return False
    
    def test_send_message_sdk(self) -> bool:
        """Test 8a: Send message using Letta SDK."""
        if not self.client or not self.agent_id:
            return self.test_send_message_http()
        
        try:
            # Modern SDK might use client.agents.messages.create() or similar
            if hasattr(self.client.agents, 'messages'):
                response = self.client.agents.messages.create(
                    agent_id=self.agent_id,
                    messages=[{"role": "user", "content": "Hello! Please respond briefly."}]
                )
                self.log_result(
                    "Send Message (SDK)",
                    True,
                    f"Got response"
                )
                return True
            else:
                return self.test_send_message_http()
            
        except Exception as e:
            error_msg = str(e)
            if "LLM" in error_msg or "API key" in error_msg.lower():
                self.log_result(
                    "Send Message (SDK)",
                    False,
                    "LLM not configured",
                    "Set ANTHROPIC_API_KEY or OPENAI_API_KEY"
                )
            else:
                self.log_result(
                    "Send Message (SDK)",
                    False,
                    f"Failed: {type(e).__name__}",
                    error_msg[:200]
                )
            return False
    
    def test_send_message_http(self) -> bool:
        """Test 8b: Send message (requires LLM API key)."""
        if not self.agent_id:
            self.log_result("Send Message", False, "No agent ID available")
            return False
        
        try:
            resp = requests.post(
                f"{self.base_url}/v1/agents/{self.agent_id}/messages",
                json={
                    "role": "user",
                    "content": "Hello! Please respond briefly."
                },
                timeout=60  # LLM calls can be slow
            )
            
            if resp.status_code == 200:
                data = resp.json()
                # Check if we got a real response or mock
                if isinstance(data, dict):
                    content = data.get('content', data.get('message', ''))
                elif isinstance(data, list) and len(data) > 0:
                    content = data[0].get('content', '') if isinstance(data[0], dict) else str(data[0])
                else:
                    content = str(data)[:100]
                
                is_mock = 'mock' in str(content).lower() or 'simulated' in str(content).lower()
                
                self.log_result(
                    "Send Message",
                    True,
                    f"Got response {'(mock - no LLM key?)' if is_mock else '(real LLM)'}",
                    str(content)[:100] if content else None
                )
                return True
            elif resp.status_code == 500 and 'LLM' in resp.text:
                self.log_result(
                    "Send Message",
                    False,
                    "LLM not configured",
                    "Set ANTHROPIC_API_KEY or OPENAI_API_KEY when starting Kelpie"
                )
                return False
            else:
                self.log_result(
                    "Send Message",
                    False,
                    f"HTTP {resp.status_code}",
                    resp.text[:200]
                )
                return False
                
        except requests.exceptions.Timeout:
            self.log_result("Send Message", False, "Timeout - LLM call took too long")
            return False
        except Exception as e:
            self.log_result("Send Message", False, str(e))
            return False
    
    def test_list_messages(self) -> bool:
        """Test 9: List conversation messages."""
        if not self.agent_id:
            self.log_result("List Messages", False, "No agent ID available")
            return False
        
        try:
            resp = requests.get(
                f"{self.base_url}/v1/agents/{self.agent_id}/messages",
                timeout=10
            )
            
            if resp.status_code == 200:
                messages = resp.json()
                count = len(messages) if isinstance(messages, list) else "unknown"
                self.log_result(
                    "List Messages",
                    True,
                    f"Found {count} messages"
                )
                return True
            else:
                self.log_result("List Messages", False, f"HTTP {resp.status_code}")
                return False
                
        except Exception as e:
            self.log_result("List Messages", False, str(e))
            return False
    
    def test_delete_agent(self) -> bool:
        """Test 10: Delete agent (cleanup)."""
        if not self.agent_id:
            self.log_result("Delete Agent", False, "No agent ID available")
            return False
        
        try:
            resp = requests.delete(
                f"{self.base_url}/v1/agents/{self.agent_id}",
                timeout=10
            )
            
            if resp.status_code in (200, 204):
                self.log_result(
                    "Delete Agent",
                    True,
                    f"Deleted agent {self.agent_id[:8]}..."
                )
                self.agent_id = None
                return True
            else:
                self.log_result("Delete Agent", False, f"HTTP {resp.status_code}")
                return False
                
        except Exception as e:
            self.log_result("Delete Agent", False, str(e))
            return False
    
    def run_all_tests(self):
        """Run all compatibility tests."""
        print("=" * 60)
        print("Letta SDK → Kelpie Migration Test")
        print("=" * 60)
        print(f"Target: {self.base_url}")
        print(f"Letta SDK: {'Available' if LETTA_SDK_AVAILABLE else 'Not installed'}")
        print("=" * 60)
        print()
        
        # Test server health first
        if not self.test_server_health():
            print("\n❌ Server not reachable. Start Kelpie first:")
            print("   cargo run -p kelpie-server")
            return 0, 1
        
        print()
        
        # Try SDK first, fall back to HTTP
        sdk_create_ok = self.test_create_agent_sdk()
        if not sdk_create_ok and not self.agent_id:
            # SDK failed, try HTTP
            print("   → Falling back to HTTP...")
            self.test_create_agent_http()
        
        # List agents
        if self.client:
            self.test_list_agents_sdk()
        else:
            self.test_list_agents_http()
        
        # Get agent
        if self.client and self.agent_id:
            self.test_get_agent_sdk()
        else:
            self.test_get_agent_http()
        
        # Memory blocks
        if self.client and self.agent_id:
            self.test_get_memory_blocks_sdk()
        else:
            self.test_get_memory_blocks_http()
        
        self.test_update_memory_block()
        
        # Tools
        self.test_list_tools()
        
        # Messaging
        if self.client and self.agent_id:
            self.test_send_message_sdk()
        else:
            self.test_send_message_http()
        
        self.test_list_messages()
        
        # Cleanup
        self.test_delete_agent()
        
        # Summary
        print()
        print("=" * 60)
        print("SUMMARY")
        print("=" * 60)
        
        passed = sum(1 for r in self.results if r.passed)
        total = len(self.results)
        
        print(f"Passed: {passed}/{total} tests")
        print()
        
        # Categorize results
        sdk_tests = [r for r in self.results if "SDK" in r.name]
        http_tests = [r for r in self.results if "HTTP" in r.name or "SDK" not in r.name]
        
        sdk_passed = sum(1 for r in sdk_tests if r.passed)
        http_passed = sum(1 for r in http_tests if r.passed)
        
        if passed == total:
            print("🎉 ALL TESTS PASSED!")
            print("   Kelpie is working as a Letta drop-in replacement.")
        elif passed >= total * 0.8:
            print("✅ MOSTLY COMPATIBLE")
            print("   Most Letta functionality works with Kelpie.")
        elif passed >= total * 0.5:
            print("⚠️  PARTIAL COMPATIBILITY")
            print("   Some features work, but there are API differences.")
        else:
            print("❌ SIGNIFICANT DIFFERENCES")
            print("   The Letta SDK may not work directly with Kelpie.")
        
        print()
        print("Breakdown:")
        if sdk_tests:
            print(f"  SDK tests: {sdk_passed}/{len(sdk_tests)} passed")
        print(f"  HTTP/Core tests: {http_passed}/{len(http_tests)} passed")
        
        # Show failed tests
        failed = [r for r in self.results if not r.passed]
        if failed:
            print()
            print("Failed tests:")
            for r in failed:
                print(f"  - {r.name}: {r.message}")
        
        print()
        print("=" * 60)
        print("RECOMMENDATION")
        print("=" * 60)
        
        if sdk_passed == len(sdk_tests) and len(sdk_tests) > 0:
            print("✅ The Letta SDK works directly with Kelpie!")
            print("   Just change your base_url to point to Kelpie.")
        elif http_passed >= len(http_tests) * 0.8:
            print("⚠️  The REST API is compatible, but the Letta SDK may have issues.")
            print("   Options:")
            print("   1. Use raw HTTP requests (requests library)")
            print("   2. Use the kelpie-client SDK instead")
            print("   3. Wait for Kelpie to update its API to match Letta SDK v1.7+")
        else:
            print("❌ There are significant API differences.")
            print("   Consider using the kelpie-client SDK for full compatibility.")
        
        return passed, total


def main():
    tester = LettaMigrationTester()
    passed, total = tester.run_all_tests()
    sys.exit(0 if passed >= total * 0.7 else 1)


if __name__ == "__main__":
    main()
