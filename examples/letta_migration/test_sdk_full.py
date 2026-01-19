#!/usr/bin/env python3
"""
Full Letta SDK Compatibility Test for Kelpie

Tests all major SDK operations including the ones that need LLM.

Usage:
    ANTHROPIC_API_KEY=... cargo run -p kelpie-server
    python test_sdk_full.py
"""

import signal
import sys
import time
from letta_client import Letta

KELPIE_URL = "http://localhost:8283"

def timeout_handler(signum, frame):
    raise TimeoutError('Operation timed out')

signal.signal(signal.SIGALRM, timeout_handler)


class SDKTester:
    def __init__(self):
        self.client = Letta(base_url=KELPIE_URL, environment='local')
        self.results = []
        self.agent = None
    
    def test(self, name, fn, timeout_sec=10):
        """Run a test with timeout."""
        try:
            signal.alarm(timeout_sec)
            start = time.time()
            result = fn()
            signal.alarm(0)
            elapsed = time.time() - start
            print(f'  ✅ {name} ({elapsed:.2f}s)')
            self.results.append((name, True, None))
            return result
        except TimeoutError:
            signal.alarm(0)
            print(f'  ❌ {name} (TIMEOUT)')
            self.results.append((name, False, 'timeout'))
            return None
        except Exception as e:
            signal.alarm(0)
            err = str(e)[:80]
            print(f'  ❌ {name}: {err}')
            self.results.append((name, False, err))
            return None
    
    def run_all(self):
        print('=' * 60)
        print('LETTA SDK FULL COMPATIBILITY TEST')
        print('=' * 60)
        print(f'Target: {KELPIE_URL}')
        print()
        
        # ===== AGENT CRUD =====
        print('AGENT OPERATIONS')
        print('-' * 40)
        
        self.agent = self.test('Create agent', lambda: self.client.agents.create(
            name='sdk-full-test',
            memory_blocks=[
                {'label': 'persona', 'value': 'You are a helpful assistant.'},
                {'label': 'human', 'value': 'The user is testing Kelpie.'}
            ]
        ))
        
        if self.agent:
            self.test('List agents', lambda: list(self.client.agents.list()))
            self.test('Get agent', lambda: self.client.agents.retrieve(self.agent.id))
            self.test('Update agent', lambda: self.client.agents.update(
                self.agent.id, 
                name='sdk-full-test-updated'
            ))
        
        print()
        
        # ===== MEMORY BLOCKS =====
        print('MEMORY BLOCK OPERATIONS')
        print('-' * 40)
        
        if self.agent:
            blocks = self.test('List blocks', 
                lambda: list(self.client.agents.blocks.list(agent_id=self.agent.id)))
            
            # Update using block LABEL (not ID) - this is how the SDK works
            self.test('Update block (by label)', lambda: self.client.agents.blocks.update(
                'persona',  # First positional arg is the LABEL
                agent_id=self.agent.id,
                value='Updated persona via Letta SDK!'
            ))
            
            # Verify the update
            def verify_update():
                blocks = list(self.client.agents.blocks.list(agent_id=self.agent.id))
                persona = next((b for b in blocks if b.label == 'persona'), None)
                if persona and 'Updated' in persona.value:
                    return True
                raise Exception('Update not reflected')
            
            self.test('Verify block update', verify_update)
        
        print()
        
        # ===== MESSAGES =====
        print('MESSAGE OPERATIONS')
        print('-' * 40)
        
        if self.agent:
            # Re-fetch agent to ensure it exists
            self.agent = self.test('Refresh agent state', 
                lambda: self.client.agents.retrieve(self.agent.id))
            
            if self.agent:
                self.test('List messages (initial)', 
                    lambda: list(self.client.agents.messages.list(agent_id=self.agent.id)))
                
                # Send message (requires LLM API key)
                def send_message():
                    response = self.client.agents.messages.create(
                        agent_id=self.agent.id,
                        messages=[{'role': 'user', 'content': 'Hello! Say hi back briefly.'}]
                    )
                    return response
                
                self.test('Send message (LLM)', send_message, timeout_sec=60)
                
                # List messages after sending
                self.test('List messages (after)', 
                    lambda: list(self.client.agents.messages.list(agent_id=self.agent.id)))
        
        print()
        
        # ===== CLEANUP =====
        print('CLEANUP')
        print('-' * 40)
        
        if self.agent:
            self.test('Delete agent', lambda: self.client.agents.delete(self.agent.id))
        
        # ===== SUMMARY =====
        print()
        print('=' * 60)
        print('SUMMARY')
        print('=' * 60)
        
        passed = sum(1 for _, p, _ in self.results if p)
        total = len(self.results)
        pct = 100 * passed // total if total > 0 else 0
        
        print(f'Results: {passed}/{total} tests passed ({pct}%)')
        print()
        
        if pct == 100:
            print('🎉 100% LETTA SDK COMPATIBLE!')
            print()
            print('The Letta SDK works perfectly with Kelpie.')
        elif pct >= 90:
            print('✅ EXCELLENT COMPATIBILITY')
            print()
            print('The Letta SDK works great with Kelpie.')
        elif pct >= 80:
            print('✅ HIGH COMPATIBILITY')
            print()
            print('Most Letta SDK features work with Kelpie.')
        else:
            print('⚠️  PARTIAL COMPATIBILITY')
        
        # Show failures
        failed = [(n, e) for n, p, e in self.results if not p]
        if failed:
            print()
            print('Failed tests:')
            for name, err in failed:
                print(f'  • {name}: {err}')
        
        return passed, total


if __name__ == '__main__':
    tester = SDKTester()
    passed, total = tester.run_all()
    sys.exit(0 if passed == total else 1)
