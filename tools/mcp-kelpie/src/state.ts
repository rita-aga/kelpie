/**
 * State management tools (AgentFS)
 *
 * TigerStyle: State operations are atomic and logged
 */

import Database from "better-sqlite3";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface StateContext {
  agentfsPath: string;
  audit: AuditContext;
}

/**
 * Create state management tools
 * Phase 4.2: state_get, state_set, state_task_start, state_task_complete, state_verified_fact
 */
export function createStateTools(context: StateContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  const dbPath = join(context.agentfsPath, "agent.db");
  const db = new Database(dbPath);

  // TigerStyle: Ensure tables exist
  db.exec(`
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
        const stmt = db.prepare("SELECT value, updated_at FROM agent_state WHERE key = ?");
        const row = stmt.get(args.key) as { value: string; updated_at: number } | undefined;

        if (!row) {
          return { success: false, error: `Key not found: ${args.key}` };
        }

        return {
          success: true,
          key: args.key,
          value: JSON.parse(row.value),
          updated_at: row.updated_at,
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
        const stmt = db.prepare(`
          INSERT INTO agent_state (key, value, updated_at)
          VALUES (?, ?, ?)
          ON CONFLICT(key) DO UPDATE SET value = ?, updated_at = ?
        `);

        const now = Date.now();
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
        const stmt = db.prepare(`
          INSERT INTO tasks (description, started_at, status)
          VALUES (?, ?, 'in_progress')
        `);

        const now = Date.now();
        const result = stmt.run(args.description, now);
        const taskId = result.lastInsertRowid;

        context.audit.log("task_start", { task_id: taskId, description: args.description });

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
      description: "Mark task as complete with verification proof (HARD: requires proof)",
      inputSchema: {
        type: "object",
        properties: {
          task_id: {
            type: "number",
            description: "Task ID to complete",
          },
          proof: {
            type: "string",
            description: "Verification proof (command output, test results, etc.)",
          },
        },
        required: ["task_id", "proof"],
      },
      handler: async (args: { task_id: number; proof: string }) => {
        // TigerStyle: HARD control - proof is required
        if (!args.proof || args.proof.trim().length === 0) {
          throw new Error("Cannot mark task complete without proof");
        }

        const stmt = db.prepare(`
          UPDATE tasks
          SET completed_at = ?, proof = ?, status = 'completed'
          WHERE id = ? AND status = 'in_progress'
        `);

        const now = Date.now();
        const result = stmt.run(now, args.proof, args.task_id);

        if (result.changes === 0) {
          throw new Error(`Task ${args.task_id} not found or already completed`);
        }

        context.audit.log("task_complete", {
          task_id: args.task_id,
          proof_length: args.proof.length,
        });

        return {
          success: true,
          task_id: args.task_id,
          completed_at: now,
          status: "completed",
        };
      },
    },
    {
      name: "state_verified_fact",
      description: "Store a verified fact (claim that has been proven by execution)",
      inputSchema: {
        type: "object",
        properties: {
          claim: {
            type: "string",
            description: "The claim being verified",
          },
          method: {
            type: "string",
            description: "Method used to verify (e.g., 'cargo test', 'manual execution')",
          },
          result: {
            type: "string",
            description: "Result of verification",
          },
        },
        required: ["claim", "method", "result"],
      },
      handler: async (args: { claim: string; method: string; result: string }) => {
        const stmt = db.prepare(`
          INSERT INTO verified_facts (claim, method, result, verified_at)
          VALUES (?, ?, ?, ?)
        `);

        const now = Date.now();
        const dbResult = stmt.run(args.claim, args.method, args.result, now);

        context.audit.log("verified_fact", {
          fact_id: dbResult.lastInsertRowid,
          claim: args.claim,
          method: args.method,
        });

        return {
          success: true,
          fact_id: dbResult.lastInsertRowid,
          claim: args.claim,
          method: args.method,
          result: args.result,
          verified_at: now,
        };
      },
    },
  ];
}
