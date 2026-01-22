/**
 * Issue Management MCP Tools
 *
 * Phase 10.2: Issue Storage Schema
 *
 * Provides tools for recording, querying, and managing codebase issues
 * discovered during agent-driven examination.
 */

import { Tool } from "@modelcontextprotocol/sdk/types.js";
import Database from "better-sqlite3";
import * as crypto from "crypto";
import * as path from "path";

// Issue severity levels
export type Severity = "critical" | "high" | "medium" | "low";

// Issue status
export type IssueStatus =
  | "open"
  | "confirmed"
  | "disputed"
  | "fixed"
  | "wont_fix";

// Issue categories
export type IssueCategory =
  | "stub" // Unimplemented code
  | "gap" // Missing functionality
  | "mismatch" // Spec vs implementation mismatch
  | "incomplete" // Partial implementation
  | "fake_dst" // DST test that isn't deterministic
  | "dead_code" // Unreachable code
  | "duplicate" // Duplicate functionality
  | "orphan" // Orphaned file/module
  | "other";

export interface Issue {
  id: string;
  found_at: number;
  found_by: string;

  // Classification
  category: IssueCategory;
  severity: Severity;

  // SHOULD (expectation)
  spec_source?: string;
  spec_requirement_id?: string;
  should_description: string;

  // IS (reality)
  is_description: string;
  location?: string;
  evidence?: string;

  // Agent analysis
  analysis: string;
  suggested_fix?: string;
  confidence?: number;

  // Status tracking
  status: IssueStatus;
  verified_by?: string;
  fixed_in_commit?: string;

  // Relationships
  related_issues?: string[];
  blocks?: string[];
  blocked_by?: string[];
}

export interface IssueFilters {
  severity?: Severity;
  status?: IssueStatus;
  category?: IssueCategory;
  spec_source?: string;
  found_by?: string;
  location_pattern?: string;
}

export interface IssueSummary {
  total: number;
  by_severity: Record<Severity, number>;
  by_status: Record<IssueStatus, number>;
  by_category: Record<string, number>;
}

export interface ExaminationEntry {
  session_id: string;
  question: string;
  module: string;
  examined_at: number;
  issues_found: number;
  notes?: string;
}

// Get database path
function getDbPath(): string {
  const workspaceRoot = process.env.WORKSPACE_ROOT || process.cwd();
  return path.join(workspaceRoot, ".agentfs", "agent.db");
}

// Initialize database connection
function getDb(): Database.Database {
  const db = new Database(getDbPath());
  db.pragma("journal_mode = WAL");
  return db;
}

// Generate unique issue ID
function generateIssueId(): string {
  const timestamp = Date.now().toString(36);
  const random = crypto.randomBytes(4).toString("hex");
  return `issue-${timestamp}-${random}`;
}

/**
 * Record a new issue discovered during examination
 */
export function recordIssue(issue: Omit<Issue, "id" | "status">): string {
  const db = getDb();
  const id = generateIssueId();

  const stmt = db.prepare(`
    INSERT INTO issues (
      id, found_at, found_by, category, severity,
      spec_source, spec_requirement_id, should_description,
      is_description, location, evidence,
      analysis, suggested_fix, confidence,
      status, related_issues, blocks, blocked_by
    ) VALUES (
      @id, @found_at, @found_by, @category, @severity,
      @spec_source, @spec_requirement_id, @should_description,
      @is_description, @location, @evidence,
      @analysis, @suggested_fix, @confidence,
      'open', @related_issues, @blocks, @blocked_by
    )
  `);

  stmt.run({
    id,
    found_at: issue.found_at || Date.now(),
    found_by: issue.found_by,
    category: issue.category,
    severity: issue.severity,
    spec_source: issue.spec_source || null,
    spec_requirement_id: issue.spec_requirement_id || null,
    should_description: issue.should_description,
    is_description: issue.is_description,
    location: issue.location || null,
    evidence: issue.evidence || null,
    analysis: issue.analysis,
    suggested_fix: issue.suggested_fix || null,
    confidence: issue.confidence || null,
    related_issues: issue.related_issues
      ? JSON.stringify(issue.related_issues)
      : null,
    blocks: issue.blocks ? JSON.stringify(issue.blocks) : null,
    blocked_by: issue.blocked_by ? JSON.stringify(issue.blocked_by) : null,
  });

  db.close();
  return id;
}

/**
 * Update an existing issue
 */
export function updateIssue(id: string, updates: Partial<Issue>): void {
  const db = getDb();

  // Build dynamic update query
  const fields: string[] = [];
  const values: Record<string, unknown> = { id };

  for (const [key, value] of Object.entries(updates)) {
    if (key === "id") continue; // Can't update ID

    if (["related_issues", "blocks", "blocked_by"].includes(key)) {
      fields.push(`${key} = @${key}`);
      values[key] = value ? JSON.stringify(value) : null;
    } else {
      fields.push(`${key} = @${key}`);
      values[key] = value;
    }
  }

  if (fields.length === 0) {
    db.close();
    return;
  }

  const stmt = db.prepare(`UPDATE issues SET ${fields.join(", ")} WHERE id = @id`);
  stmt.run(values);
  db.close();
}

/**
 * Query issues with filters
 */
export function queryIssues(filters: IssueFilters = {}): Issue[] {
  const db = getDb();

  const conditions: string[] = [];
  const values: Record<string, unknown> = {};

  if (filters.severity) {
    conditions.push("severity = @severity");
    values.severity = filters.severity;
  }

  if (filters.status) {
    conditions.push("status = @status");
    values.status = filters.status;
  }

  if (filters.category) {
    conditions.push("category = @category");
    values.category = filters.category;
  }

  if (filters.spec_source) {
    conditions.push("spec_source = @spec_source");
    values.spec_source = filters.spec_source;
  }

  if (filters.found_by) {
    conditions.push("found_by = @found_by");
    values.found_by = filters.found_by;
  }

  if (filters.location_pattern) {
    conditions.push("location LIKE @location_pattern");
    values.location_pattern = `%${filters.location_pattern}%`;
  }

  const whereClause =
    conditions.length > 0 ? `WHERE ${conditions.join(" AND ")}` : "";

  const stmt = db.prepare(`
    SELECT * FROM issues ${whereClause}
    ORDER BY 
      CASE severity 
        WHEN 'critical' THEN 1 
        WHEN 'high' THEN 2 
        WHEN 'medium' THEN 3 
        WHEN 'low' THEN 4 
      END,
      found_at DESC
  `);

  const rows = stmt.all(values) as Record<string, unknown>[];
  db.close();

  return rows.map((row) => ({
    ...row,
    related_issues: row.related_issues
      ? JSON.parse(row.related_issues as string)
      : undefined,
    blocks: row.blocks ? JSON.parse(row.blocks as string) : undefined,
    blocked_by: row.blocked_by
      ? JSON.parse(row.blocked_by as string)
      : undefined,
  })) as Issue[];
}

/**
 * Get issue summary statistics
 */
export function getIssueSummary(): IssueSummary {
  const db = getDb();

  const total = db
    .prepare("SELECT COUNT(*) as count FROM issues")
    .get() as { count: number };

  const bySeverity = db
    .prepare("SELECT severity, COUNT(*) as count FROM issues GROUP BY severity")
    .all() as { severity: Severity; count: number }[];

  const byStatus = db
    .prepare("SELECT status, COUNT(*) as count FROM issues GROUP BY status")
    .all() as { status: IssueStatus; count: number }[];

  const byCategory = db
    .prepare("SELECT category, COUNT(*) as count FROM issues GROUP BY category")
    .all() as { category: string; count: number }[];

  db.close();

  return {
    total: total.count,
    by_severity: Object.fromEntries(
      bySeverity.map((r) => [r.severity, r.count])
    ) as Record<Severity, number>,
    by_status: Object.fromEntries(
      byStatus.map((r) => [r.status, r.count])
    ) as Record<IssueStatus, number>,
    by_category: Object.fromEntries(byCategory.map((r) => [r.category, r.count])),
  };
}

/**
 * Get a specific issue by ID
 */
export function getIssue(id: string): Issue | null {
  const db = getDb();
  const stmt = db.prepare("SELECT * FROM issues WHERE id = ?");
  const row = stmt.get(id) as Record<string, unknown> | undefined;
  db.close();

  if (!row) return null;

  return {
    ...row,
    related_issues: row.related_issues
      ? JSON.parse(row.related_issues as string)
      : undefined,
    blocks: row.blocks ? JSON.parse(row.blocks as string) : undefined,
    blocked_by: row.blocked_by
      ? JSON.parse(row.blocked_by as string)
      : undefined,
  } as Issue;
}

/**
 * Log an examination for thoroughness verification
 */
export function logExamination(entry: ExaminationEntry): void {
  const db = getDb();

  const stmt = db.prepare(`
    INSERT INTO examination_log (session_id, question, module, examined_at, issues_found, notes)
    VALUES (@session_id, @question, @module, @examined_at, @issues_found, @notes)
  `);

  stmt.run({
    session_id: entry.session_id,
    question: entry.question,
    module: entry.module,
    examined_at: entry.examined_at || Date.now(),
    issues_found: entry.issues_found || 0,
    notes: entry.notes || null,
  });

  db.close();
}

/**
 * Get examination log for a session
 */
export function getExaminationLog(sessionId: string): ExaminationEntry[] {
  const db = getDb();

  const stmt = db.prepare(`
    SELECT * FROM examination_log 
    WHERE session_id = ?
    ORDER BY examined_at ASC
  `);

  const rows = stmt.all(sessionId) as ExaminationEntry[];
  db.close();
  return rows;
}

/**
 * Check thoroughness - what partitions were examined
 */
export function checkThoroughness(
  sessionId: string,
  expectedModules: string[]
): {
  complete: boolean;
  examined: string[];
  missing: string[];
  coverage_percent: number;
} {
  const log = getExaminationLog(sessionId);
  const examined = new Set(log.map((e) => e.module));
  const expected = new Set(expectedModules);

  const missing = expectedModules.filter((m) => !examined.has(m));

  return {
    complete: missing.length === 0,
    examined: Array.from(examined),
    missing,
    coverage_percent:
      expected.size > 0 ? (examined.size / expected.size) * 100 : 100,
  };
}

// MCP Tool Definitions
export const issueTools: Tool[] = [
  {
    name: "issue_record",
    description:
      "Record a new codebase issue discovered during examination. Returns the issue ID.",
    inputSchema: {
      type: "object",
      properties: {
        found_by: {
          type: "string",
          description: "Session/agent ID that found the issue",
        },
        category: {
          type: "string",
          enum: [
            "stub",
            "gap",
            "mismatch",
            "incomplete",
            "fake_dst",
            "dead_code",
            "duplicate",
            "orphan",
            "other",
          ],
          description: "Issue category",
        },
        severity: {
          type: "string",
          enum: ["critical", "high", "medium", "low"],
          description: "Issue severity",
        },
        should_description: {
          type: "string",
          description: "What SHOULD be true (the expectation)",
        },
        is_description: {
          type: "string",
          description: "What IS true (the reality)",
        },
        analysis: {
          type: "string",
          description: "Why this is an issue",
        },
        location: {
          type: "string",
          description: "File:line location (optional)",
        },
        evidence: {
          type: "string",
          description: "Code snippet or other evidence (optional)",
        },
        spec_source: {
          type: "string",
          description:
            "Spec source e.g. 'letta_openapi', 'dst_rules' (optional)",
        },
        suggested_fix: {
          type: "string",
          description: "Suggested fix (optional)",
        },
        confidence: {
          type: "number",
          description: "Confidence 0-1 (optional)",
        },
      },
      required: [
        "found_by",
        "category",
        "severity",
        "should_description",
        "is_description",
        "analysis",
      ],
    },
  },
  {
    name: "issue_update",
    description: "Update an existing issue's status or other fields",
    inputSchema: {
      type: "object",
      properties: {
        id: {
          type: "string",
          description: "Issue ID to update",
        },
        status: {
          type: "string",
          enum: ["open", "confirmed", "disputed", "fixed", "wont_fix"],
          description: "New status",
        },
        verified_by: {
          type: "string",
          description: "Agent/human who verified",
        },
        fixed_in_commit: {
          type: "string",
          description: "Commit SHA that fixed the issue",
        },
      },
      required: ["id"],
    },
  },
  {
    name: "issue_query",
    description:
      "Query issues with filters. Returns list of issues sorted by severity.",
    inputSchema: {
      type: "object",
      properties: {
        severity: {
          type: "string",
          enum: ["critical", "high", "medium", "low"],
        },
        status: {
          type: "string",
          enum: ["open", "confirmed", "disputed", "fixed", "wont_fix"],
        },
        category: {
          type: "string",
        },
        spec_source: {
          type: "string",
        },
        location_pattern: {
          type: "string",
          description: "Pattern to match in location field",
        },
      },
    },
  },
  {
    name: "issue_summary",
    description: "Get summary statistics of all issues",
    inputSchema: {
      type: "object",
      properties: {},
    },
  },
  {
    name: "examination_log",
    description: "Log that a module was examined (for thoroughness verification)",
    inputSchema: {
      type: "object",
      properties: {
        session_id: {
          type: "string",
          description: "Current session ID",
        },
        question: {
          type: "string",
          description: "The question being answered",
        },
        module: {
          type: "string",
          description: "Module/partition that was examined",
        },
        issues_found: {
          type: "number",
          description: "Number of issues found in this module",
        },
        notes: {
          type: "string",
          description: "Optional examination notes",
        },
      },
      required: ["session_id", "question", "module"],
    },
  },
  {
    name: "thoroughness_check",
    description:
      "Check if examination was thorough - reports missing modules",
    inputSchema: {
      type: "object",
      properties: {
        session_id: {
          type: "string",
          description: "Session ID to check",
        },
        expected_modules: {
          type: "array",
          items: { type: "string" },
          description: "List of modules that should have been examined",
        },
      },
      required: ["session_id", "expected_modules"],
    },
  },
];

/**
 * Handle issue tool calls
 */
export async function handleIssueTool(
  name: string,
  args: Record<string, unknown>
): Promise<unknown> {
  switch (name) {
    case "issue_record":
      return {
        id: recordIssue({
          found_at: Date.now(),
          found_by: args.found_by as string,
          category: args.category as IssueCategory,
          severity: args.severity as Severity,
          should_description: args.should_description as string,
          is_description: args.is_description as string,
          analysis: args.analysis as string,
          location: args.location as string | undefined,
          evidence: args.evidence as string | undefined,
          spec_source: args.spec_source as string | undefined,
          suggested_fix: args.suggested_fix as string | undefined,
          confidence: args.confidence as number | undefined,
        }),
      };

    case "issue_update":
      updateIssue(args.id as string, args);
      return { success: true };

    case "issue_query":
      return queryIssues(args as IssueFilters);

    case "issue_summary":
      return getIssueSummary();

    case "examination_log":
      logExamination({
        session_id: args.session_id as string,
        question: args.question as string,
        module: args.module as string,
        examined_at: Date.now(),
        issues_found: (args.issues_found as number) || 0,
        notes: args.notes as string | undefined,
      });
      return { success: true };

    case "thoroughness_check":
      return checkThoroughness(
        args.session_id as string,
        args.expected_modules as string[]
      );

    default:
      throw new Error(`Unknown issue tool: ${name}`);
  }
}
