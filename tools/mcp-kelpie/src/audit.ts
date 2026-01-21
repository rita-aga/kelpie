/**
 * Audit logging for MCP server
 *
 * TigerStyle: Every tool call is logged to audit trail
 */

import Database from "better-sqlite3";
import { join } from "path";

export interface AuditContext {
  log: (event: string, data: Record<string, any>) => void;
}

/**
 * Create audit logger
 * TigerStyle: All tool calls are logged for traceability
 */
export function createAuditLogger(agentfsPath: string): AuditContext {
  const dbPath = join(agentfsPath, "agent.db");
  const db = new Database(dbPath);

  // Ensure audit_log table exists (should already exist from Phase 1)
  db.exec(`
    CREATE TABLE IF NOT EXISTS audit_log (
      id INTEGER PRIMARY KEY AUTOINCREMENT,
      timestamp INTEGER NOT NULL,
      event TEXT NOT NULL,
      data TEXT NOT NULL
    );
  `);

  return {
    log: (event: string, data: Record<string, any>): void => {
      const stmt = db.prepare(`
        INSERT INTO audit_log (timestamp, event, data)
        VALUES (?, ?, ?)
      `);

      stmt.run(Date.now(), event, JSON.stringify(data));
    },
  };
}
