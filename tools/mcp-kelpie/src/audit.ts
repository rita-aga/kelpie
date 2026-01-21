/**
 * Audit logging for MCP server
 *
 * TigerStyle: Every tool call is logged to audit trail
 */

import Database from "better-sqlite3";
import { join } from "path";
import { execSync } from "child_process";

export interface AuditContext {
  log: (event: string, data: Record<string, any>, result?: any) => void;
  codebasePath: string;
}

/**
 * Get current git HEAD SHA for audit trail
 */
function getGitSha(codebasePath: string): string | null {
  try {
    const sha = execSync("git rev-parse HEAD", {
      cwd: codebasePath,
      encoding: "utf-8",
    }).trim();
    return sha;
  } catch (error) {
    return null;
  }
}

/**
 * Create audit logger
 * TigerStyle: All tool calls are logged for traceability
 *
 * Plan requirement: Log result and git_sha per call
 */
export function createAuditLogger(agentfsPath: string, codebasePath: string): AuditContext {
  const dbPath = join(agentfsPath, "agent.db");
  const db = new Database(dbPath);

  // Ensure audit_log table exists
  // Added result and git_sha columns per plan requirement
  db.exec(`
    CREATE TABLE IF NOT EXISTS audit_log (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      timestamp INTEGER NOT NULL,
      event TEXT NOT NULL,
      data TEXT NOT NULL,
      result TEXT,
      git_sha TEXT
    );
  `);

  return {
    codebasePath,
    log: (event: string, data: Record<string, any>, result?: any): void => {
      const stmt = db.prepare(`
        INSERT INTO audit_log (timestamp, event, data, result, git_sha)
        VALUES (?, ?, ?, ?, ?)
      `);

      const gitSha = getGitSha(codebasePath);
      const resultJson = result !== undefined ? JSON.stringify(result) : null;

      stmt.run(Date.now(), event, JSON.stringify(data), resultJson, gitSha);
    },
  };
}
