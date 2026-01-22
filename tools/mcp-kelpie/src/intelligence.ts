/**
 * Codebase Intelligence MCP Tools
 *
 * Provides codebase exploration and issue tracking tools.
 *
 * NOTE: The deep Python-based examination was removed in Phase 16.5.
 * Agents should use CLI tools directly for verification (Phase 16.6):
 *   - cargo test -p kelpie-dst --release
 *   - cargo test stateright_* -- --ignored
 *   - cargo kani --package kelpie-core
 */

import { Tool } from "@modelcontextprotocol/sdk/types.js";
import * as path from "path";
import Database from "better-sqlite3";

// Context for intelligence tools
export interface IntelligenceContext {
  codebasePath: string;
  indexesPath: string;
  agentfsPath: string;
  rlmEnvPath: string;
}

/**
 * Quick scope analysis to determine relevant modules
 */
function quickScopeAnalysis(question: string): {
  relevant_modules: string[];
  suggested_commands: string[];
} {
  const questionLower = question.toLowerCase();
  const modules: string[] = [];
  const commands: string[] = [];

  // DST-related
  if (
    questionLower.includes("dst") ||
    questionLower.includes("deterministic") ||
    questionLower.includes("simulation") ||
    questionLower.includes("test coverage")
  ) {
    modules.push(
      "crates/kelpie-dst",
      "crates/kelpie-storage",
      "crates/kelpie-runtime"
    );
    commands.push(
      "cargo test -p kelpie-dst --release",
      "DST_SEED=12345 cargo test -p kelpie-dst"
    );
  }

  // API/Letta
  if (
    questionLower.includes("letta") ||
    questionLower.includes("api") ||
    questionLower.includes("compatibility") ||
    questionLower.includes("endpoint")
  ) {
    modules.push(
      "crates/kelpie-server/src/api",
      "crates/kelpie-server/src/models"
    );
    commands.push(
      "cargo test -p kelpie-server api",
      "grep -r 'TODO\\|FIXME' crates/kelpie-server/src/api/"
    );
  }

  // Storage
  if (
    questionLower.includes("storage") ||
    questionLower.includes("fdb") ||
    questionLower.includes("foundationdb")
  ) {
    modules.push("crates/kelpie-storage", "crates/kelpie-server/src/storage");
    commands.push("cargo test -p kelpie-storage");
  }

  // Actor/runtime
  if (
    questionLower.includes("actor") ||
    questionLower.includes("runtime") ||
    questionLower.includes("lifecycle")
  ) {
    modules.push("crates/kelpie-runtime", "crates/kelpie-server/src/actor");
    commands.push("cargo test -p kelpie-runtime");
  }

  // TigerStyle compliance
  if (
    questionLower.includes("tigerstyle") ||
    questionLower.includes("unwrap") ||
    questionLower.includes("assert")
  ) {
    commands.push(
      "grep -r 'unwrap()\\|expect(' crates/ --include='*.rs' | head -20",
      "cargo clippy --workspace -- -D warnings"
    );
  }

  // Default
  if (modules.length === 0) {
    modules.push(
      "crates/kelpie-core",
      "crates/kelpie-server",
      "crates/kelpie-runtime"
    );
    commands.push("cargo test --workspace", "cargo clippy --workspace");
  }

  return {
    relevant_modules: [...new Set(modules)],
    suggested_commands: [...new Set(commands)],
  };
}

/**
 * Get issue dashboard from AgentFS
 */
function getIssueDashboard(agentfsPath: string): {
  total: number;
  by_severity: Record<string, number>;
  by_status: Record<string, number>;
  recent: Array<{
    id: string;
    severity: string;
    should: string;
    location: string;
  }>;
} {
  try {
    const db = new Database(path.join(agentfsPath, "agent.db"));

    const total = db
      .prepare("SELECT COUNT(*) as count FROM issues")
      .get() as { count: number };

    const bySeverity = db
      .prepare(
        "SELECT severity, COUNT(*) as count FROM issues GROUP BY severity"
      )
      .all() as { severity: string; count: number }[];

    const byStatus = db
      .prepare("SELECT status, COUNT(*) as count FROM issues GROUP BY status")
      .all() as { status: string; count: number }[];

    const recent = db
      .prepare(
        `
      SELECT id, severity, should_description as should, location 
      FROM issues 
      ORDER BY found_at DESC 
      LIMIT 10
    `
      )
      .all() as {
      id: string;
      severity: string;
      should: string;
      location: string;
    }[];

    db.close();

    return {
      total: total.count,
      by_severity: Object.fromEntries(
        bySeverity.map((r) => [r.severity, r.count])
      ),
      by_status: Object.fromEntries(byStatus.map((r) => [r.status, r.count])),
      recent,
    };
  } catch {
    // AgentFS not initialized
    return {
      total: 0,
      by_severity: {},
      by_status: {},
      recent: [],
    };
  }
}

/**
 * Create intelligence tools
 */
export function createIntelligenceTools(_ctx: IntelligenceContext): Tool[] {
  return [
    {
      name: "codebase_scope",
      description: `Analyze a question to determine relevant codebase modules and suggested CLI commands.

Returns:
- relevant_modules: Directories to examine
- suggested_commands: CLI commands to run for verification

NOTE: For deep analysis, run the suggested commands directly in terminal.`,
      inputSchema: {
        type: "object",
        properties: {
          question: {
            type: "string",
            description: "The question to analyze",
          },
        },
        required: ["question"],
      },
    },
    {
      name: "issue_dashboard",
      description:
        "Get a dashboard view of all recorded issues - counts by severity/status and recent issues",
      inputSchema: {
        type: "object",
        properties: {},
      },
    },
    {
      name: "examination_history",
      description: "Get history of codebase examinations and their coverage",
      inputSchema: {
        type: "object",
        properties: {
          session_id: {
            type: "string",
            description: "Optional session ID to filter by",
          },
          limit: {
            type: "number",
            description: "Max number of records to return (default 20)",
          },
        },
      },
    },
  ];
}

/**
 * Handle intelligence tool calls
 */
export async function handleIntelligenceTool(
  ctx: IntelligenceContext,
  name: string,
  args: Record<string, unknown>
): Promise<unknown> {
  switch (name) {
    case "codebase_scope": {
      const question = args.question as string;
      return quickScopeAnalysis(question);
    }

    case "issue_dashboard": {
      return getIssueDashboard(ctx.agentfsPath);
    }

    case "examination_history": {
      const sessionId = args.session_id as string | undefined;
      const limit = (args.limit as number) || 20;

      try {
        const db = new Database(path.join(ctx.agentfsPath, "agent.db"));

        let query = `
          SELECT session_id, question, module, examined_at, issues_found, notes
          FROM examination_log
        `;
        const params: unknown[] = [];

        if (sessionId) {
          query += " WHERE session_id = ?";
          params.push(sessionId);
        }

        query += ` ORDER BY examined_at DESC LIMIT ?`;
        params.push(limit);

        const rows = db.prepare(query).all(...params);
        db.close();

        return {
          count: rows.length,
          examinations: rows,
        };
      } catch {
        return {
          count: 0,
          examinations: [],
        };
      }
    }

    default:
      throw new Error(`Unknown intelligence tool: ${name}`);
  }
}
