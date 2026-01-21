/**
 * State management tools (AgentFS-compatible)
 *
 * Phase 16.4: Uses AgentFS SDK when available, falls back to SQLite
 * Reference: https://github.com/tursodatabase/agentfs
 *
 * Key namespacing follows AgentFS conventions:
 * - state:{key} - General agent state
 * - task:{id} - Task tracking
 * - vfs:fact:{id} - Verified facts (VFS = Virtual File System namespace)
 *
 * TigerStyle: State operations are atomic and logged
 */

import Database from "better-sqlite3";
import { join } from "path";
import { execSync } from "child_process";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface StateContext {
  agentfsPath: string;
  codebasePath: string;
  audit: AuditContext;
}

/**
 * Create state management tools using AgentFS-compatible KV storage
 * Phase 4.2: state_get, state_set, state_task_start, state_task_complete, state_verified_fact
 */
export function createStateTools(
  context: StateContext
): Array<Tool & { handler: (args: any) => Promise<any> }> {
  const dbPath = join(context.agentfsPath, "agent.db");
  const db = new Database(dbPath);

  // AgentFS-compatible schema: single KV table with namespaced keys
  // This follows the AgentFS SQLite schema pattern
  db.exec(`
    CREATE TABLE IF NOT EXISTS kv (
      key TEXT PRIMARY KEY,
      value TEXT NOT NULL,
      created_at INTEGER NOT NULL,
      updated_at INTEGER NOT NULL
    );

    CREATE TABLE IF NOT EXISTS tool_calls (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      tool TEXT NOT NULL,
      started_at REAL NOT NULL,
      ended_at REAL,
      input TEXT,
      output TEXT,
      status TEXT DEFAULT 'pending'
    );

    -- Legacy tables for backward compatibility (will be migrated)
    CREATE TABLE IF NOT EXISTS agent_state (
      key TEXT PRIMARY KEY,
      value TEXT NOT NULL,
      updated_at INTEGER NOT NULL
    );

    CREATE TABLE IF NOT EXISTS verified_facts (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      claim TEXT NOT NULL,
      method TEXT NOT NULL,
      result TEXT NOT NULL,
      verified_at INTEGER NOT NULL
    );

    CREATE TABLE IF NOT EXISTS tasks (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      description TEXT NOT NULL,
      started_at INTEGER NOT NULL,
      completed_at INTEGER,
      proof TEXT,
      status TEXT NOT NULL DEFAULT 'in_progress'
    );
  `);

  // Helper: AgentFS-style KV operations
  const kv = {
    get: (key: string): any => {
      const stmt = db.prepare("SELECT value FROM kv WHERE key = ?");
      const row = stmt.get(key) as { value: string } | undefined;
      return row ? JSON.parse(row.value) : null;
    },
    set: (key: string, value: any): void => {
      const now = Date.now();
      const stmt = db.prepare(`
        INSERT INTO kv (key, value, created_at, updated_at)
        VALUES (?, ?, ?, ?)
        ON CONFLICT(key) DO UPDATE SET value = ?, updated_at = ?
      `);
      const json = JSON.stringify(value);
      stmt.run(key, json, now, now, json, now);
    },
  };

  // Helper: Record tool call (AgentFS timeline pattern)
  const recordToolCall = (
    tool: string,
    startedAt: number,
    endedAt: number,
    input: any,
    output: any
  ) => {
    const stmt = db.prepare(`
      INSERT INTO tool_calls (tool, started_at, ended_at, input, output, status)
      VALUES (?, ?, ?, ?, ?, 'success')
    `);
    stmt.run(
      tool,
      startedAt / 1000,
      endedAt / 1000,
      JSON.stringify(input),
      JSON.stringify(output)
    );
  };

  return [
    {
      name: "state_get",
      description: "Get value from agent state by key",
      inputSchema: {
        type: "object",
        properties: {
          key: {
            type: "string",
            description: "State key to retrieve",
          },
        },
        required: ["key"],
      },
      handler: async (args: { key: string }) => {
        const value = kv.get(`state:${args.key}`);

        if (value === null) {
          // Fallback to legacy table
          const stmt = db.prepare(
            "SELECT value, updated_at FROM agent_state WHERE key = ?"
          );
          const row = stmt.get(args.key) as
            | { value: string; updated_at: number }
            | undefined;

          if (!row) {
            return { success: false, error: `Key not found: ${args.key}` };
          }

          return {
            success: true,
            key: args.key,
            value: JSON.parse(row.value),
            updated_at: row.updated_at,
          };
        }

        return {
          success: true,
          key: args.key,
          value: value.value,
          updated_at: value.updated_at,
        };
      },
    },
    {
      name: "state_set",
      description: "Set value in agent state",
      inputSchema: {
        type: "object",
        properties: {
          key: {
            type: "string",
            description: "State key to set",
          },
          value: {
            description: "Value to store (any JSON-serializable type)",
          },
        },
        required: ["key", "value"],
      },
      handler: async (args: { key: string; value: any }) => {
        const now = Date.now();

        // Write to AgentFS-style KV
        kv.set(`state:${args.key}`, {
          value: args.value,
          updated_at: now,
        });

        // Also write to legacy table for compatibility
        const stmt = db.prepare(`
          INSERT INTO agent_state (key, value, updated_at)
          VALUES (?, ?, ?)
          ON CONFLICT(key) DO UPDATE SET value = ?, updated_at = ?
        `);
        const valueJson = JSON.stringify(args.value);
        stmt.run(args.key, valueJson, now, valueJson, now);

        context.audit.log("state_set", { key: args.key });

        return {
          success: true,
          key: args.key,
          value: args.value,
          updated_at: now,
        };
      },
    },
    {
      name: "state_task_start",
      description: "Start a new task and log to audit trail",
      inputSchema: {
        type: "object",
        properties: {
          description: {
            type: "string",
            description: "Task description",
          },
        },
        required: ["description"],
      },
      handler: async (args: { description: string }) => {
        const now = Date.now();

        // Write to legacy table (gets ID)
        const stmt = db.prepare(`
          INSERT INTO tasks (description, started_at, status)
          VALUES (?, ?, 'in_progress')
        `);
        const result = stmt.run(args.description, now);
        const taskId = result.lastInsertRowid;

        // Also write to AgentFS-style KV
        kv.set(`task:${taskId}`, {
          id: taskId,
          description: args.description,
          started_at: now,
          status: "in_progress",
        });

        // Record in tool timeline
        recordToolCall("task_start", now, now, { description: args.description }, { task_id: taskId });

        context.audit.log("task_start", {
          task_id: taskId,
          description: args.description,
        });

        return {
          success: true,
          task_id: taskId,
          description: args.description,
          started_at: now,
          status: "in_progress",
        };
      },
    },
    {
      name: "state_task_complete",
      description:
        "Mark task as complete with verification proof (HARD: requires proof)",
      inputSchema: {
        type: "object",
        properties: {
          task_id: {
            type: "number",
            description: "Task ID to complete",
          },
          proof: {
            type: "string",
            description:
              "Verification proof (command output, test results, etc.)",
          },
        },
        required: ["task_id", "proof"],
      },
      handler: async (args: { task_id: number; proof: string }) => {
        // TigerStyle: HARD control - proof is required
        if (!args.proof || args.proof.trim().length === 0) {
          throw new Error("Cannot mark task complete without proof");
        }

        // HARD CONTROL: Enforce P0 constraints before marking complete
        const constraintErrors: string[] = [];

        try {
          execSync("cargo test --all", {
            cwd: context.codebasePath,
            stdio: "pipe",
            timeout: 300000,
          });
        } catch {
          constraintErrors.push(
            "P0 VIOLATION: Tests failing (cargo test --all failed)"
          );
        }

        try {
          execSync("cargo clippy --all-targets --all-features -- -D warnings", {
            cwd: context.codebasePath,
            stdio: "pipe",
            timeout: 180000,
          });
        } catch {
          constraintErrors.push("P0 VIOLATION: Clippy warnings exist");
        }

        try {
          execSync("cargo fmt --check", {
            cwd: context.codebasePath,
            stdio: "pipe",
          });
        } catch {
          constraintErrors.push(
            "P0 VIOLATION: Code not formatted (run cargo fmt)"
          );
        }

        if (constraintErrors.length > 0) {
          throw new Error(
            `Cannot mark task complete - P0 constraint violations:\n${constraintErrors.join("\n")}`
          );
        }

        const now = Date.now();

        // Update legacy table
        const stmt = db.prepare(`
          UPDATE tasks
          SET completed_at = ?, proof = ?, status = 'completed'
          WHERE id = ? AND status = 'in_progress'
        `);
        const result = stmt.run(now, args.proof, args.task_id);

        if (result.changes === 0) {
          throw new Error(`Task ${args.task_id} not found or already completed`);
        }

        // Update AgentFS-style KV
        const existing = kv.get(`task:${args.task_id}`);
        if (existing) {
          kv.set(`task:${args.task_id}`, {
            ...existing,
            completed_at: now,
            proof: args.proof,
            status: "completed",
          });
        }

        // Record in tool timeline
        recordToolCall(
          "task_complete",
          now,
          now,
          { task_id: args.task_id, proof_length: args.proof.length },
          { success: true, p0_checks_passed: true }
        );

        context.audit.log(
          "task_complete",
          {
            task_id: args.task_id,
            proof_length: args.proof.length,
          },
          { success: true, p0_checks_passed: true }
        );

        return {
          success: true,
          task_id: args.task_id,
          completed_at: now,
          status: "completed",
          p0_checks_passed: true,
        };
      },
    },
    {
      name: "state_verified_fact",
      description:
        "Store a verified fact (claim that has been proven by execution)",
      inputSchema: {
        type: "object",
        properties: {
          claim: {
            type: "string",
            description: "The claim being verified",
          },
          method: {
            type: "string",
            description:
              "Method used to verify (e.g., 'cargo test', 'manual execution')",
          },
          result: {
            type: "string",
            description: "Result of verification",
          },
        },
        required: ["claim", "method", "result"],
      },
      handler: async (args: { claim: string; method: string; result: string }) => {
        const now = Date.now();

        // Write to legacy table (gets ID)
        const stmt = db.prepare(`
          INSERT INTO verified_facts (claim, method, result, verified_at)
          VALUES (?, ?, ?, ?)
        `);
        const dbResult = stmt.run(args.claim, args.method, args.result, now);
        const factId = dbResult.lastInsertRowid;

        // Also write to AgentFS-style KV with VFS namespace
        kv.set(`vfs:fact:${factId}`, {
          id: factId,
          claim: args.claim,
          method: args.method,
          result: args.result,
          verified_at: now,
        });

        // Record in tool timeline
        recordToolCall(
          "verified_fact",
          now,
          now,
          { claim: args.claim, method: args.method },
          { fact_id: factId, result: args.result }
        );

        context.audit.log("verified_fact", {
          fact_id: factId,
          claim: args.claim,
          method: args.method,
        });

        return {
          success: true,
          fact_id: factId,
          claim: args.claim,
          method: args.method,
          result: args.result,
          verified_at: now,
        };
      },
    },
  ];
}
