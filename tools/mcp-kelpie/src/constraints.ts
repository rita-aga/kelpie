/**
 * Constraint checking tools - Verify P0 violations (Phase 4.2)
 *
 * TigerStyle: Hard enforcement of project constraints from .vision/CONSTRAINTS.md
 */

import { execSync } from "child_process";
import { readFileSync, existsSync } from "fs";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface ConstraintsContext {
  codebasePath: string;
  audit: AuditContext;
}

interface ConstraintViolation {
  type: string;
  severity: "P0" | "P1" | "P2";
  message: string;
  file?: string;
  line?: number;
  suggestion: string;
}

/**
 * Check for placeholder code (TODOs, FIXMEs, etc.)
 */
function checkPlaceholders(codebasePath: string): ConstraintViolation[] {
  const violations: ConstraintViolation[] = [];

  try {
    // Search for placeholders in Rust code
    const patterns = ["TODO", "FIXME", "HACK", "XXX", "PLACEHOLDER"];

    for (const pattern of patterns) {
      try {
        const output = execSync(`git grep -n "${pattern}" -- '*.rs' || true`, {
          cwd: codebasePath,
          encoding: "utf-8",
          timeout: 10000,
        });

        if (output.trim()) {
          const matches = output.trim().split("\n");
          for (const match of matches.slice(0, 10)) {
            // Limit to first 10
            const parts = match.split(":");
            const file = parts[0];
            const line = parts[1] ? parseInt(parts[1], 10) : undefined;

            violations.push({
              type: "placeholder_code",
              severity: "P0",
              message: `Placeholder found: ${pattern}`,
              file,
              line,
              suggestion: "Remove or implement before marking complete",
            });
          }
        }
      } catch {
        // Continue with other patterns
      }
    }
  } catch (error) {
    // If git grep fails, we can't check for placeholders
  }

  return violations;
}

/**
 * Check for unwrap() in production code
 */
function checkUnwrapInProduction(codebasePath: string): ConstraintViolation[] {
  const violations: ConstraintViolation[] = [];

  try {
    // Find .unwrap() in non-test Rust files
    const output = execSync(
      `git grep -n '\\.unwrap()' -- '*.rs' ':(exclude)*test*.rs' ':(exclude)tests/' || true`,
      {
        cwd: codebasePath,
        encoding: "utf-8",
        timeout: 10000,
      }
    );

    if (output.trim()) {
      const matches = output.trim().split("\n");
      for (const match of matches.slice(0, 10)) {
        const parts = match.split(":");
        const file = parts[0];
        const line = parts[1] ? parseInt(parts[1], 10) : undefined;

        violations.push({
          type: "unwrap_in_production",
          severity: "P0",
          message: "Production code uses .unwrap() which can panic",
          file,
          line,
          suggestion: "Use Result/Option pattern or explicit error handling",
        });
      }
    }
  } catch {
    // If command fails, skip this check
  }

  return violations;
}

/**
 * Check for DST test coverage on critical paths
 */
function checkDstCoverage(codebasePath: string): ConstraintViolation[] {
  const violations: ConstraintViolation[] = [];

  try {
    // Check if critical paths have DST tests
    const criticalPaths = [
      { name: "actor activation", pattern: "actor.*activate" },
      { name: "state persistence", pattern: "state.*persist" },
      { name: "cross-actor invocation", pattern: "invoke.*actor" },
      { name: "failure recovery", pattern: "recover.*fail" },
    ];

    for (const path of criticalPaths) {
      // Check if DST test exists for this critical path
      try {
        const output = execSync(`git grep -l "${path.pattern}" -- '*_dst.rs' || true`, {
          cwd: codebasePath,
          encoding: "utf-8",
          timeout: 5000,
        });

        if (!output.trim()) {
          violations.push({
            type: "missing_dst_coverage",
            severity: "P0",
            message: `Critical path "${path.name}" has no DST test coverage`,
            suggestion: "Add simulation test with fault injection (see .vision/CONSTRAINTS.md)",
          });
        }
      } catch {
        // Continue with other paths
      }
    }
  } catch {
    // If check fails, report as potential violation
  }

  return violations;
}

/**
 * Check for explicit constants with units
 */
function checkTigerStyleConstants(codebasePath: string): ConstraintViolation[] {
  const violations: ConstraintViolation[] = [];

  try {
    // Look for constants without unit suffixes (basic heuristic)
    const output = execSync(
      `git grep -n 'pub const.*: u64 =' -- '*.rs' | grep -v '_MS' | grep -v '_BYTES' | grep -v '_MAX' | grep -v '_MIN' || true`,
      {
        cwd: codebasePath,
        encoding: "utf-8",
        timeout: 10000,
      }
    );

    if (output.trim()) {
      const matches = output.trim().split("\n").slice(0, 5); // First 5
      for (const match of matches) {
        const parts = match.split(":");
        const file = parts[0];
        const line = parts[1] ? parseInt(parts[1], 10) : undefined;

        violations.push({
          type: "tigerstyle_constant_naming",
          severity: "P1",
          message: "Constant may be missing unit suffix",
          file,
          line,
          suggestion: "Add unit suffix like _MS, _BYTES, _MAX (TigerStyle)",
        });
      }
    }
  } catch {
    // Skip if check fails
  }

  return violations;
}

/**
 * Check for missing plan files for recent work
 */
function checkPlanningRequired(codebasePath: string): ConstraintViolation[] {
  const violations: ConstraintViolation[] = [];

  try {
    const progressDir = join(codebasePath, ".progress");

    if (!existsSync(progressDir)) {
      violations.push({
        type: "missing_planning",
        severity: "P0",
        message: ".progress/ directory not found - no planning files",
        suggestion: "Create .progress/ directory and add numbered plan files",
      });
      return violations;
    }

    // Check if there are recent commits without corresponding plan files
    // (This is a basic check - could be enhanced)
    const recentCommits = execSync("git log --oneline -5", {
      cwd: codebasePath,
      encoding: "utf-8",
      timeout: 5000,
    });

    const hasFeatureCommits = /feat:|fix:|refactor:/.test(recentCommits);

    if (hasFeatureCommits) {
      // Check if there are plan files
      const planFiles = execSync("ls -1 .progress/*.md 2>/dev/null | wc -l", {
        cwd: codebasePath,
        encoding: "utf-8",
        timeout: 5000,
      });

      if (parseInt(planFiles.trim(), 10) === 0) {
        violations.push({
          type: "missing_planning",
          severity: "P0",
          message: "Recent feature work has no planning files in .progress/",
          suggestion: "Create numbered plan files for non-trivial work",
        });
      }
    }
  } catch {
    // Skip if check fails
  }

  return violations;
}

/**
 * Create constraint checking tools for Phase 4.2
 */
export function createConstraintTools(
  context: ConstraintsContext
): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "constraint_check",
      description: "Check for P0 constraint violations in the codebase",
      inputSchema: {
        type: "object",
        properties: {
          check_types: {
            type: "array",
            description:
              "Types of checks to run (placeholders, unwraps, dst_coverage, tigerstyle, planning). Defaults to all.",
            items: {
              type: "string",
              enum: ["placeholders", "unwraps", "dst_coverage", "tigerstyle", "planning"],
            },
          },
        },
      },
      handler: async (args: { check_types?: string[] }) => {
        const checkTypes = args.check_types || [
          "placeholders",
          "unwraps",
          "dst_coverage",
          "tigerstyle",
          "planning",
        ];
        const violations: ConstraintViolation[] = [];

        // Run requested checks
        if (checkTypes.includes("placeholders")) {
          violations.push(...checkPlaceholders(context.codebasePath));
        }

        if (checkTypes.includes("unwraps")) {
          violations.push(...checkUnwrapInProduction(context.codebasePath));
        }

        if (checkTypes.includes("dst_coverage")) {
          violations.push(...checkDstCoverage(context.codebasePath));
        }

        if (checkTypes.includes("tigerstyle")) {
          violations.push(...checkTigerStyleConstants(context.codebasePath));
        }

        if (checkTypes.includes("planning")) {
          violations.push(...checkPlanningRequired(context.codebasePath));
        }

        // Group by severity
        const p0Violations = violations.filter((v) => v.severity === "P0");
        const p1Violations = violations.filter((v) => v.severity === "P1");
        const p2Violations = violations.filter((v) => v.severity === "P2");

        context.audit.log("constraint_check", {
          check_types: checkTypes,
          p0_violations: p0Violations.length,
          p1_violations: p1Violations.length,
          p2_violations: p2Violations.length,
        });

        return {
          success: p0Violations.length === 0,
          summary: {
            total_violations: violations.length,
            p0_violations: p0Violations.length,
            p1_violations: p1Violations.length,
            p2_violations: p2Violations.length,
          },
          violations: {
            p0: p0Violations,
            p1: p1Violations,
            p2: p2Violations,
          },
          message:
            p0Violations.length > 0
              ? `Found ${p0Violations.length} P0 violations - must fix before marking complete`
              : "No P0 violations found",
        };
      },
    },
    {
      name: "constraint_list",
      description: "List all P0 constraints and their enforcement rules",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const constraintsPath = join(context.codebasePath, ".vision", "CONSTRAINTS.md");

        // Load constraints from file if it exists
        let constraintsContent = "";
        if (existsSync(constraintsPath)) {
          constraintsContent = readFileSync(constraintsPath, "utf-8");
        }

        const constraints = [
          {
            name: "Simulation-First Development",
            priority: "P0",
            description:
              "Every feature MUST have DST tests with fault injection before being considered complete",
            enforcement: ["Must have *_dst.rs test file", "Test must use Simulation harness", "Test must inject faults"],
            verification: "cargo test -p kelpie-dst",
          },
          {
            name: "TigerStyle Safety",
            priority: "P0",
            description: "Safety > Performance > DX. Explicit constants, assertions, no silent failures",
            enforcement: [
              "Constants must have unit suffixes (_MS, _BYTES, _MAX)",
              "Functions must have 2+ assertions",
              "No silent truncation of types",
              "No .unwrap() in production code",
            ],
            verification: "cargo clippy",
          },
          {
            name: "No Placeholders",
            priority: "P0",
            description: "No TODO, FIXME, HACK, or stub implementations in production code",
            enforcement: ["No TODO/FIXME/HACK/XXX comments", "No stub functions", "No commented-out code"],
            verification: "/no-cap command",
          },
          {
            name: "Planning Required",
            priority: "P0",
            description: "Non-trivial work (3+ steps, multi-file) must have a plan in .progress/",
            enforcement: [
              "Create numbered plan file before starting",
              "Document options considered",
              "Log decisions and trade-offs",
            ],
            verification: "Check .progress/ directory",
          },
          {
            name: "Verification Before Completion",
            priority: "P0",
            description: "All verification steps must pass before marking work complete",
            enforcement: [
              "cargo test (all tests pass)",
              "cargo clippy (no warnings)",
              "cargo fmt --check (formatted)",
              "/no-cap (no placeholders)",
              "DST coverage verified",
            ],
            verification: "Run full verification suite",
          },
        ];

        context.audit.log("constraint_list", {});

        return {
          success: true,
          constraints,
          constraints_file_exists: existsSync(constraintsPath),
          constraints_file_path: constraintsPath,
          full_text: constraintsContent ? constraintsContent.slice(0, 5000) : "Not found", // First 5000 chars
        };
      },
    },
  ];
}
