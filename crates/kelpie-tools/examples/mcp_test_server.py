#!/usr/bin/env python3
"""
Simple MCP test server for testing kelpie-tools MCP client.

This implements a minimal MCP server with a few test tools:
- echo: Returns the input message
- add: Adds two numbers
- read_file: Simulates reading a file

Run: python3 mcp_test_server.py
"""

import json
import sys


def read_message():
    """Read a JSON-RPC message from stdin."""
    line = sys.stdin.readline()
    if not line:
        return None
    return json.loads(line.strip())


def write_message(msg):
    """Write a JSON-RPC message to stdout."""
    sys.stdout.write(json.dumps(msg) + "\n")
    sys.stdout.flush()


def handle_initialize(request):
    """Handle initialize request."""
    return {
        "jsonrpc": "2.0",
        "id": request["id"],
        "result": {
            "protocolVersion": "2024-11-05",
            "capabilities": {
                "tools": {"listChanged": False}
            },
            "serverInfo": {
                "name": "test-mcp-server",
                "version": "1.0.0"
            }
        }
    }


def handle_tools_list(request):
    """Handle tools/list request."""
    return {
        "jsonrpc": "2.0",
        "id": request["id"],
        "result": {
            "tools": [
                {
                    "name": "echo",
                    "description": "Echo back the input message",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "message": {
                                "type": "string",
                                "description": "Message to echo"
                            }
                        },
                        "required": ["message"]
                    }
                },
                {
                    "name": "add",
                    "description": "Add two numbers",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "a": {"type": "number", "description": "First number"},
                            "b": {"type": "number", "description": "Second number"}
                        },
                        "required": ["a", "b"]
                    }
                },
                {
                    "name": "read_file",
                    "description": "Read a file (simulated)",
                    "inputSchema": {
                        "type": "object",
                        "properties": {
                            "path": {"type": "string", "description": "File path"}
                        },
                        "required": ["path"]
                    }
                }
            ]
        }
    }


def handle_tools_call(request):
    """Handle tools/call request."""
    params = request.get("params", {})
    tool_name = params.get("name")
    arguments = params.get("arguments", {})

    if tool_name == "echo":
        message = arguments.get("message", "")
        return {
            "jsonrpc": "2.0",
            "id": request["id"],
            "result": {
                "content": [{"type": "text", "text": f"Echo: {message}"}]
            }
        }

    elif tool_name == "add":
        a = arguments.get("a", 0)
        b = arguments.get("b", 0)
        return {
            "jsonrpc": "2.0",
            "id": request["id"],
            "result": {
                "content": [{"type": "text", "text": f"Result: {a + b}"}]
            }
        }

    elif tool_name == "read_file":
        path = arguments.get("path", "")
        return {
            "jsonrpc": "2.0",
            "id": request["id"],
            "result": {
                "content": [{"type": "text", "text": f"Contents of {path}: [simulated file content]"}]
            }
        }

    else:
        return {
            "jsonrpc": "2.0",
            "id": request["id"],
            "error": {
                "code": -32601,
                "message": f"Unknown tool: {tool_name}"
            }
        }


def main():
    """Main server loop."""
    sys.stderr.write("MCP test server started\n")
    sys.stderr.flush()

    while True:
        request = read_message()
        if request is None:
            break

        method = request.get("method")
        sys.stderr.write(f"Received: {method}\n")
        sys.stderr.flush()

        if method == "initialize":
            response = handle_initialize(request)
        elif method == "tools/list":
            response = handle_tools_list(request)
        elif method == "tools/call":
            response = handle_tools_call(request)
        elif method == "notifications/initialized":
            # Notification, no response needed
            continue
        else:
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "error": {
                    "code": -32601,
                    "message": f"Method not found: {method}"
                }
            }

        write_message(response)


if __name__ == "__main__":
    main()
