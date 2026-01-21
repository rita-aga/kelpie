/**
 * Integrity tools - Hard enforcement of verification requirements (Phase 4.7)
 *
 * TigerStyle: Hard controls that agents cannot bypass
 * - mark_phase_complete requires evidence
 * - start_plan_session re-verifies all completions
 */

import { execSync } from "child_process";
import Database from "better-sqlite3";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface IntegrityContext {
  codebasePath: string;
  agentfsPath: string;
  audit: AuditContext;
}

interface Evidence {
  verification_commands: Array<{ command: string; expected: string }>;
  files_created?: string[];
  description?: string;
}

interface VerificationResult {
  command: string;
  expected: string;
  actual: string;
  passed: boolean;
}

/**
 * Execute command and check if output matches expected
 */
function executeAndMatch(command: string, expected: string, cwd: string): VerificationResult {
  try {
    const actual = execSync(command, {
      cwd,
      encoding: "utf-8",
      timeout: 60000, // 1 minute
      maxBuffer: 1024 * 1024, // 1MB
    }).trim();

    // Simple string match - can be made more sophisticated
    const passed = actual.includes(expected) || actual === expected;

    return { command, expected, actual: actual.slice(0, 500), passed };
  } catch (error: any) {
    return {
      command,
      expected,
      actual: error.message || "Command failed",
      passed: false,
    };
  }
}

/**
 * Get current git SHA
 */
function getCurrentGitSha(cwd: string): string {
  try {
    return execSync("git rev-parse HEAD", {
      cwd,
      encoding: "utf-8",
    }).trim();
  } catch {
    return "unknown";
  }
}

/**
 * Create integrity tools for Phase 4.7
 */
export function createIntegrityTools(context: IntegrityContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  const dbPath = join(context.agentfsPath, "agent.db");
  const db = new Database(dbPath);

  // Ensure completions table exists
  db.exec(`
    CREATE TABLE IF NOT EXISTS phase_completions (
      phase TEXT PRIMARY KEY,
      claimed_at INTEGER NOT NULL,
      git_sha TEXT NOT NULL,
      evidence TEXT NOT NULL,
      verification_results TEXT NOT NULL,
      status TEXT NOT NULL
    );
  `);

  return [
    {
      name: "mark_phase_complete",
      description: "Mark phase complete with verification evidence (HARD: requires proof)",
      inputSchema: {
        type: "object",
        properties: {
          phase: {
            type: "string",
            description: "Phase identifier (e.g., 'phase_2_1_symbols')",
          },
          evidence: {
            type: "object",
            description: "Evidence object with verification_commands array",
            properties: {
              verification_commands: {
                type: "array",
                items: {
                  type: "object",
                  properties: {
                    command: { type: "string" },
                    expected: { type: "string" },
                  },
                },
              },
              files_created: {
                type: "array",
                items: { type: "string" },
              },
              description: { type: "string" },
            },
            required: ["verification_commands"],
          },
        },
        required: ["phase", "evidence"],
      },
      handler: async (args: { phase: string; evidence: Evidence }) => {
        // TigerStyle: HARD control - evidence is required
        if (!args.evidence || !args.evidence.verification_commands || args.evidence.verification_commands.length === 0) {
          throw new Error("Cannot mark phase complete without verification commands");
        }

        // HARD: System re-runs verifications NOW
        const results: VerificationResult[] = [];
        for (const cmd of args.evidence.verification_commands) {
          const result = executeAndMatch(cmd.command, cmd.expected, context.codebasePath);
          results.push(result);

          if (!result.passed) {
            throw new Error(
              `Verification failed: ${cmd.command} expected "${cmd.expected}" but got "${result.actual.slice(0, 100)}"`
            );
          }
        }

        // HARD: Only if all pass, store completion with proof
        const now = Date.now();
        const gitSha = getCurrentGitSha(context.codebasePath);

        const stmt = db.prepare(`
          INSERT INTO phase_completions (phase, claimed_at, git_sha, evidence, verification_results, status)
          VALUES (?, ?, ?, ?, ?, 'verified')
          ON CONFLICT(phase) DO UPDATE SET
            claimed_at = ?,
            git_sha = ?,
            evidence = ?,
            verification_results = ?,
            status = 'verified'
        `);

        stmt.run(
          args.phase,
          now,
          gitSha,
          JSON.stringify(args.evidence),
          JSON.stringify(results),
          now,
          gitSha,
          JSON.stringify(args.evidence),
          JSON.stringify(results)
        );

        context.audit.log("mark_phase_complete", {
          phase: args.phase,
          verifications: results.length,
          git_sha: gitSha,
        });

        return {
          success: true,
          phase: args.phase,
          claimed_at: now,
          git_sha: gitSha,
          verification_results: results,
          message: `Phase ${args.phase} verified and marked complete`,
        };
      },
    },
    {
      name: "start_plan_session",
      description: "Start plan session with automatic re-verification of all completions (HARD)",
      inputSchema: {
        type: "object",
        properties: {
          plan_id: {
            type: "string",
            description: "Plan identifier",
          },
        },
        required: ["plan_id"],
      },
      handler: async (args: { plan_id: string }) => {
        // Load all completions for this plan
        const stmt = db.prepare(`
          SELECT * FROM phase_completions
          WHERE phase LIKE ?
        `);

        const completions = stmt.all(`${args.plan_id}_%`) as Array<{
          phase: string;
          claimed_at: number;
          git_sha: string;
          evidence: string;
          verification_results: string;
          status: string;
        }>;

        const verificationReport: Array<{
          phase: string;
          command: string;
          expected: string;
          actual: string;
          passed: boolean;
          original_result?: string;
        }> = [];

        // HARD: System automatically re-verifies ALL claimed completions
        for (const completion of completions) {
          if (completion.status !== "verified") continue;

          const evidence: Evidence = JSON.parse(completion.evidence);
          const originalResults: VerificationResult[] = JSON.parse(completion.verification_results);

          for (const cmd of evidence.verification_commands) {
            const result = executeAndMatch(cmd.command, cmd.expected, context.codebasePath);

            const originalResult = originalResults.find((r) => r.command === cmd.command);

            verificationReport.push({
              phase: completion.phase,
              command: result.command,
              expected: result.expected,
              actual: result.actual,
              passed: result.passed,
              original_result: originalResult?.actual,
            });

            if (!result.passed) {
              // HARD: Mark phase as UNVERIFIED - previous agent lied or code changed
              const updateStmt = db.prepare(`
                UPDATE phase_completions
                SET status = 'unverified'
                WHERE phase = ?
              `);
              updateStmt.run(completion.phase);
            }
          }
        }

        const failedPhases = verificationReport.filter((r) => !r.passed);
        const uniqueFailedPhases = [...new Set(failedPhases.map((r) => r.phase))];

        context.audit.log("start_plan_session", {
          plan_id: args.plan_id,
          phases_checked: completions.length,
          verifications_passed: verificationReport.filter((r) => r.passed).length,
          verifications_failed: failedPhases.length,
        });

        return {
          success: true,
          plan_id: args.plan_id,
          session_started: Date.now(),
          verification_report: verificationReport.slice(0, 50), // First 50 verifications
          phases_verified: verificationReport.filter((r) => r.passed).length,
          phases_failed: failedPhases.length,
          phases_needing_attention: uniqueFailedPhases,
          message:
            failedPhases.length > 0
              ? `WARNING: ${failedPhases.length} verifications failed. Review phases_needing_attention before proceeding.`
              : `All ${verificationReport.length} verifications passed. Safe to continue.`,
        };
      },
    },
  ];
}
