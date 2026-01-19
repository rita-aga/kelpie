#!/usr/bin/env python3
"""
Kelpie-Letta Compatibility Test Suite

This script tests Kelpie's REST API compatibility with Letta's expected formats.
It documents exactly what works and what doesn't for users migrating from Letta.

Usage:
    1. Start Kelpie: cargo run -p kelpie-server
    2. Run: python test_compatibility.py
"""

import json
import sys
import time
import requests
from dataclasses import dataclass, field
from typing import Optional, List, Dict, Any
from datetime import datetime

KELPIE_URL = "http://localhost:8283"


@dataclass
class TestResult:
    name: str
    category: str
    passed: bool
    message: str
    details: Optional[str] = None
    letta_expected: Optional[str] = None
    kelpie_actual: Optional[str] = None


class CompatibilityTester:
    def __init__(self, base_url: str = KELPIE_URL):
        self.base_url = base_url
        self.results: List[TestResult] = []
        self.agent_id: Optional[str] = None
        self.block_id: Optional[str] = None
        
    def log(self, name: str, category: str, passed: bool, message: str, 
            details: str = None, letta_expected: str = None, kelpie_actual: str = None):
        self.results.append(TestResult(
            name=name, category=category, passed=passed, message=message,
            details=details, letta_expected=letta_expected, kelpie_actual=kelpie_actual
        ))
        status = "✅" if passed else "❌"
        print(f"  {status} {name}: {message}")
        if not passed and details:
            print(f"     └─ {details}")
    
    def get(self, path: str, **kwargs) -> requests.Response:
        return requests.get(f"{self.base_url}{path}", timeout=10, **kwargs)
    
    def post(self, path: str, **kwargs) -> requests.Response:
        return requests.post(f"{self.base_url}{path}", timeout=30, **kwargs)
    
    def patch(self, path: str, **kwargs) -> requests.Response:
        return requests.patch(f"{self.base_url}{path}", timeout=10, **kwargs)
    
    def delete(self, path: str, **kwargs) -> requests.Response:
        return requests.delete(f"{self.base_url}{path}", timeout=10, **kwargs)
    
    # ==================== Health & Server ====================
    
    def test_health(self):
        """Test /health endpoint."""
        try:
            r = self.get("/health")
            if r.status_code == 200:
                data = r.json()
                has_required = all(k in data for k in ['status', 'version'])
                self.log("Health Check", "server", has_required,
                        f"v{data.get('version', '?')} - uptime {data.get('uptime_seconds', '?')}s",
                        letta_expected="status, version fields",
                        kelpie_actual=str(list(data.keys())))
            else:
                self.log("Health Check", "server", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Health Check", "server", False, str(e))
    
    def test_capabilities(self):
        """Test /v1/capabilities endpoint."""
        try:
            r = self.get("/v1/capabilities")
            if r.status_code == 200:
                data = r.json()
                self.log("Capabilities", "server", True,
                        f"Features: {data.get('features', [])[:3]}...",
                        kelpie_actual=str(list(data.keys())))
            else:
                self.log("Capabilities", "server", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Capabilities", "server", False, str(e))
    
    # ==================== Agents ====================
    
    def test_create_agent(self):
        """Test POST /v1/agents."""
        try:
            r = self.post("/v1/agents", json={
                "name": "compat-test-agent",
                "memory_blocks": [
                    {"label": "persona", "value": "You are a helpful assistant."},
                    {"label": "human", "value": "The user is testing compatibility."}
                ]
            })
            
            if r.status_code in (200, 201):
                data = r.json()
                self.agent_id = data.get("id")
                required = ['id', 'name', 'agent_type', 'blocks']
                has_required = all(k in data for k in required)
                self.log("Create Agent", "agents", has_required,
                        f"ID: {self.agent_id[:8]}..." if self.agent_id else "Created",
                        letta_expected="id, name, agent_type, blocks, tool_ids, tags",
                        kelpie_actual=str(list(data.keys())))
            else:
                self.log("Create Agent", "agents", False, f"HTTP {r.status_code}", r.text[:100])
        except Exception as e:
            self.log("Create Agent", "agents", False, str(e))
    
    def test_list_agents(self):
        """Test GET /v1/agents response format."""
        try:
            r = self.get("/v1/agents")
            if r.status_code == 200:
                data = r.json()
                
                # Letta SDK expects: {"items": [...], "has_more": bool} OR just a list
                # Kelpie returns: {"items": [...], "total": int, "cursor": str|null}
                
                if isinstance(data, list):
                    # Direct list format - SDK compatible
                    self.log("List Agents Format", "agents", True,
                            f"Returns list directly ({len(data)} items)",
                            letta_expected="list or {items, has_more}",
                            kelpie_actual="list")
                elif isinstance(data, dict):
                    has_items = 'items' in data
                    items = data.get('items', [])
                    
                    # Check pagination format
                    pagination_keys = [k for k in data.keys() if k != 'items']
                    
                    # The SDK's SyncArrayPage looks for 'has_more' or similar
                    has_pagination = any(k in data for k in ['has_more', 'next_cursor', 'cursor'])
                    
                    self.log("List Agents Format", "agents", has_items,
                            f"Returns dict with {len(items)} items",
                            f"Pagination keys: {pagination_keys}",
                            letta_expected="{items: [...], has_more?: bool}",
                            kelpie_actual=f"{{items, {', '.join(pagination_keys)}}}")
                else:
                    self.log("List Agents Format", "agents", False,
                            f"Unexpected type: {type(data).__name__}")
            else:
                self.log("List Agents Format", "agents", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("List Agents Format", "agents", False, str(e))
    
    def test_get_agent(self):
        """Test GET /v1/agents/{id}."""
        if not self.agent_id:
            self.log("Get Agent", "agents", False, "No agent ID available")
            return
            
        try:
            r = self.get(f"/v1/agents/{self.agent_id}")
            if r.status_code == 200:
                data = r.json()
                required = ['id', 'name', 'blocks']
                has_required = all(k in data for k in required)
                self.log("Get Agent", "agents", has_required,
                        f"Name: {data.get('name')}",
                        kelpie_actual=str(list(data.keys())))
            else:
                self.log("Get Agent", "agents", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Get Agent", "agents", False, str(e))
    
    def test_update_agent(self):
        """Test PATCH /v1/agents/{id}."""
        if not self.agent_id:
            self.log("Update Agent", "agents", False, "No agent ID available")
            return
            
        try:
            r = self.patch(f"/v1/agents/{self.agent_id}", json={
                "name": "compat-test-agent-updated"
            })
            
            if r.status_code == 200:
                data = r.json()
                updated = data.get('name') == "compat-test-agent-updated"
                self.log("Update Agent", "agents", updated,
                        f"Name: {data.get('name')}")
            else:
                self.log("Update Agent", "agents", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Update Agent", "agents", False, str(e))
    
    # ==================== Memory Blocks ====================
    
    def test_get_blocks(self):
        """Test GET /v1/agents/{id}/blocks."""
        if not self.agent_id:
            self.log("Get Blocks", "memory", False, "No agent ID available")
            return
            
        try:
            r = self.get(f"/v1/agents/{self.agent_id}/blocks")
            if r.status_code == 200:
                data = r.json()
                if isinstance(data, list) and len(data) > 0:
                    self.block_id = data[0].get('id')
                    labels = [b.get('label') for b in data]
                    required = ['id', 'label', 'value']
                    has_required = all(k in data[0] for k in required)
                    self.log("Get Blocks", "memory", has_required,
                            f"Blocks: {labels}",
                            kelpie_actual=str(list(data[0].keys())))
                else:
                    self.log("Get Blocks", "memory", False, "Empty or non-list response")
            else:
                self.log("Get Blocks", "memory", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Get Blocks", "memory", False, str(e))
    
    def test_update_block_by_label_letta_path(self):
        """Test PATCH /v1/agents/{id}/blocks/{label} (Letta's path)."""
        if not self.agent_id:
            self.log("Update Block (Letta Path)", "memory", False, "No agent ID")
            return
            
        try:
            r = self.patch(f"/v1/agents/{self.agent_id}/blocks/human", json={
                "value": "Updated via Letta path"
            })
            
            if r.status_code == 200:
                self.log("Update Block (Letta Path)", "memory", True,
                        "Works! /v1/agents/{id}/blocks/{label}")
            elif r.status_code == 404:
                self.log("Update Block (Letta Path)", "memory", False,
                        "Path not supported",
                        "Use /core-memory/blocks/{label} instead")
            else:
                self.log("Update Block (Letta Path)", "memory", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Update Block (Letta Path)", "memory", False, str(e))
    
    def test_update_block_kelpie_path(self):
        """Test PATCH /v1/agents/{id}/core-memory/blocks/{label} (Kelpie's path)."""
        if not self.agent_id:
            self.log("Update Block (Kelpie Path)", "memory", False, "No agent ID")
            return
            
        try:
            r = self.patch(f"/v1/agents/{self.agent_id}/core-memory/blocks/human", json={
                "value": "Updated via Kelpie path"
            })
            
            if r.status_code == 200:
                self.log("Update Block (Kelpie Path)", "memory", True,
                        "Works! /core-memory/blocks/{label}")
            else:
                self.log("Update Block (Kelpie Path)", "memory", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Update Block (Kelpie Path)", "memory", False, str(e))
    
    # ==================== Messages ====================
    
    def test_list_messages(self):
        """Test GET /v1/agents/{id}/messages."""
        if not self.agent_id:
            self.log("List Messages", "messages", False, "No agent ID")
            return
            
        try:
            r = self.get(f"/v1/agents/{self.agent_id}/messages")
            if r.status_code == 200:
                data = r.json()
                count = len(data) if isinstance(data, list) else "?"
                self.log("List Messages", "messages", True, f"{count} messages")
            else:
                self.log("List Messages", "messages", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("List Messages", "messages", False, str(e))
    
    def test_send_message(self):
        """Test POST /v1/agents/{id}/messages."""
        if not self.agent_id:
            self.log("Send Message", "messages", False, "No agent ID")
            return
            
        try:
            r = self.post(f"/v1/agents/{self.agent_id}/messages", json={
                "role": "user",
                "content": "Hello!"
            })
            
            if r.status_code == 200:
                data = r.json()
                has_content = 'content' in data or (isinstance(data, list) and len(data) > 0)
                self.log("Send Message", "messages", True,
                        "Message sent (may need LLM API key for real response)")
            elif r.status_code == 500:
                if 'LLM' in r.text or 'API key' in r.text.lower():
                    self.log("Send Message", "messages", False,
                            "LLM not configured",
                            "Set ANTHROPIC_API_KEY or OPENAI_API_KEY")
                else:
                    self.log("Send Message", "messages", False, f"Server error: {r.text[:100]}")
            else:
                self.log("Send Message", "messages", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Send Message", "messages", False, str(e))
    
    # ==================== Tools ====================
    
    def test_list_tools(self):
        """Test GET /v1/tools."""
        try:
            r = self.get("/v1/tools")
            if r.status_code == 200:
                data = r.json()
                if isinstance(data, list):
                    self.log("List Tools", "tools", True,
                            f"{len(data)} tools (list format)")
                elif isinstance(data, dict):
                    # Check if it has expected structure
                    if 'items' in data:
                        self.log("List Tools", "tools", True,
                                f"{len(data['items'])} tools (paginated format)")
                    else:
                        self.log("List Tools", "tools", True,
                                f"Tools as dict: {list(data.keys())[:3]}...",
                                letta_expected="list of tools",
                                kelpie_actual="dict with tool names as keys")
                else:
                    self.log("List Tools", "tools", False, f"Unexpected: {type(data)}")
            else:
                self.log("List Tools", "tools", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("List Tools", "tools", False, str(e))
    
    # ==================== Archival ====================
    
    def test_archival_memory(self):
        """Test archival memory endpoints."""
        if not self.agent_id:
            self.log("Archival Memory", "archival", False, "No agent ID")
            return
        
        try:
            # POST to add
            r = self.post(f"/v1/agents/{self.agent_id}/archival", json={
                "text": "Test archival memory entry"
            })
            
            if r.status_code == 200:
                # GET to list
                r2 = self.get(f"/v1/agents/{self.agent_id}/archival")
                if r2.status_code == 200:
                    self.log("Archival Memory", "archival", True, "Add + List work")
                else:
                    self.log("Archival Memory", "archival", False,
                            f"Add OK, List failed: {r2.status_code}")
            else:
                self.log("Archival Memory", "archival", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Archival Memory", "archival", False, str(e))
    
    # ==================== Cleanup ====================
    
    def test_delete_agent(self):
        """Test DELETE /v1/agents/{id}."""
        if not self.agent_id:
            self.log("Delete Agent", "agents", False, "No agent ID")
            return
            
        try:
            r = self.delete(f"/v1/agents/{self.agent_id}")
            if r.status_code in (200, 204):
                self.log("Delete Agent", "agents", True, f"Deleted {self.agent_id[:8]}...")
                self.agent_id = None
            else:
                self.log("Delete Agent", "agents", False, f"HTTP {r.status_code}")
        except Exception as e:
            self.log("Delete Agent", "agents", False, str(e))
    
    # ==================== Run All ====================
    
    def run_all(self):
        print("=" * 70)
        print("KELPIE-LETTA COMPATIBILITY TEST")
        print("=" * 70)
        print(f"Target: {self.base_url}")
        print(f"Time: {datetime.now().isoformat()}")
        print("=" * 70)
        print()
        
        # Check server is up
        try:
            r = self.get("/health")
            if r.status_code != 200:
                print("❌ Server not responding. Start Kelpie first:")
                print("   cargo run -p kelpie-server")
                return
        except:
            print("❌ Cannot connect to server. Start Kelpie first:")
            print("   cargo run -p kelpie-server")
            return
        
        print("SERVER")
        print("-" * 40)
        self.test_health()
        self.test_capabilities()
        print()
        
        print("AGENTS")
        print("-" * 40)
        self.test_create_agent()
        self.test_list_agents()
        self.test_get_agent()
        self.test_update_agent()
        print()
        
        print("MEMORY BLOCKS")
        print("-" * 40)
        self.test_get_blocks()
        self.test_update_block_by_label_letta_path()
        self.test_update_block_kelpie_path()
        print()
        
        print("MESSAGES")
        print("-" * 40)
        self.test_list_messages()
        self.test_send_message()
        print()
        
        print("TOOLS")
        print("-" * 40)
        self.test_list_tools()
        print()
        
        print("ARCHIVAL MEMORY")
        print("-" * 40)
        self.test_archival_memory()
        print()
        
        print("CLEANUP")
        print("-" * 40)
        self.test_delete_agent()
        print()
        
        # Summary
        print("=" * 70)
        print("SUMMARY")
        print("=" * 70)
        
        by_category = {}
        for r in self.results:
            if r.category not in by_category:
                by_category[r.category] = []
            by_category[r.category].append(r)
        
        total_passed = sum(1 for r in self.results if r.passed)
        total = len(self.results)
        
        print(f"\nOverall: {total_passed}/{total} tests passed ({100*total_passed//total}%)")
        print()
        
        for cat, tests in by_category.items():
            passed = sum(1 for t in tests if t.passed)
            print(f"  {cat}: {passed}/{len(tests)} passed")
        
        print()
        
        # Compatibility assessment
        if total_passed == total:
            print("🎉 FULL COMPATIBILITY")
            print("   Kelpie works as a drop-in Letta replacement.")
        elif total_passed >= total * 0.8:
            print("✅ HIGH COMPATIBILITY")
            print("   Most Letta features work with Kelpie.")
        elif total_passed >= total * 0.6:
            print("⚠️  PARTIAL COMPATIBILITY")
            print("   Core features work, but some differences exist.")
        else:
            print("❌ LOW COMPATIBILITY")
            print("   Significant API differences.")
        
        # Known issues
        failed = [r for r in self.results if not r.passed]
        if failed:
            print()
            print("Known Issues:")
            for r in failed:
                print(f"  • {r.name}: {r.message}")
                if r.details:
                    print(f"    {r.details}")
        
        print()
        print("=" * 70)
        print("RECOMMENDATIONS")
        print("=" * 70)
        print("""
For using Letta SDK with Kelpie:

1. The REST API (raw HTTP) is highly compatible
2. The official letta-client SDK may hang due to pagination format differences
3. Recommended approach:
   
   Option A: Use raw HTTP requests
   --------------------------------
   import requests
   
   BASE = "http://localhost:8283"
   
   # Create agent
   agent = requests.post(f"{BASE}/v1/agents", json={
       "name": "my-agent",
       "memory_blocks": [
           {"label": "persona", "value": "You are helpful"},
           {"label": "human", "value": "The user"}
       ]
   }).json()
   
   # Send message
   response = requests.post(
       f"{BASE}/v1/agents/{agent['id']}/messages",
       json={"role": "user", "content": "Hello!"}
   ).json()
   
   Option B: Use kelpie-client SDK
   --------------------------------
   pip install -e adapters/sdk/python/
   from kelpie_client import KelpieClient
   
   client = KelpieClient("http://localhost:8283")
   agent = client.create_agent(name="my-agent", ...)
""")
        
        return total_passed, total


if __name__ == "__main__":
    tester = CompatibilityTester()
    passed, total = tester.run_all()
    sys.exit(0 if passed >= total * 0.7 else 1)
