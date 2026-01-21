/**
 * Verification tools - running tests and verifying claims
 *
 * TigerStyle: Verification by execution, not by trusting claims
 */

import { execSync } from "child_process";
import { readFileSync } from "fs";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface VerificationContext {
  codebasePath: string;
  indexesPath: string;
  audit: AuditContext;
}

/**
 * Execute command and capture output
 * TigerStyle: Timeout and error handling
 */
function executeCommand(command: string, cwd: string, timeoutMs: number = 120000): { success: boolean; output: string; error?: string } {
  try {
    const output = execSync(command, {
      cwd,
      encoding: "utf-8",
      timeout: timeoutMs,
      maxBuffer: 10 * 1024 * 1024, // 10MB buffer
    });
    return { success: true, output };
  } catch (error: any) {
    return {
      success: false,
      output: error.stdout || "",
      error: error.stderr || error.message,
    };
  }
}

/**
 * Load tests index
 */
function loadTestsIndex(indexesPath: string): any {
  const testsPath = join(indexesPath, "structural", "tests.json");
  const content = readFileSync(testsPath, "utf-8");
  return JSON.parse(content);
}

/**
 * Create verification tools
 * Phase 4.4: verify_by_tests, verify_claim
 */
export function createVerificationTools(context: VerificationContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "verify_by_tests",
      description: "Find and run tests related to a topic, return results",
      inputSchema: {
        type: "object",
        properties: {
          topic: {
            type: "string",
            description: "Topic to find tests for (e.g., 'storage', 'actor')",
          },
          type: {
            type: "string",
            description: "Optional: test type filter (unit, dst, integration)",
          },
        },
        required: ["topic"],
      },
      handler: async (args: { topic: string; type?: string }) => {
        const tests = loadTestsIndex(context.indexesPath);

        // Find tests matching topic
        let matches = tests.tests.filter((t: any) => t.topics && t.topics.includes(args.topic));

        // Filter by type if specified
        if (args.type) {
          matches = matches.filter((t: any) => t.type === args.type);
        }

        if (matches.length === 0) {
          return {
            success: false,
            error: `No tests found for topic: ${args.topic}`,
            topic: args.topic,
          };
        }

        // Run each test and collect results
        const results = [];
        for (const test of matches.slice(0, 10)) {
          // Limit to first 10 tests
          const result = executeCommand(test.command, context.codebasePath, 60000); // 1 minute per test

          results.push({
            name: test.name,
            file: test.file,
            command: test.command,
            success: result.success,
            output: result.output.slice(0, 1000), // Truncate output
            error: result.error,
          });
        }

        const passedCount = results.filter((r) => r.success).length;
        const failedCount = results.length - passedCount;

        context.audit.log("verify_by_tests", {
          topic: args.topic,
          tests_run: results.length,
          passed: passedCount,
          failed: failedCount,
        });

        return {
          success: failedCount === 0,
          topic: args.topic,
          tests_run: results.length,
          passed: passedCount,
          failed: failedCount,
          results,
        };
      },
    },
    {
      name: "verify_claim",
      description: "Verify a claim by executing appropriate verification method",
      inputSchema: {
        type: "object",
        properties: {
          claim: {
            type: "string",
            description: "Claim to verify (e.g., 'All tests pass', 'Feature X is implemented')",
          },
          method: {
            type: "string",
            description: "Verification method (e.g., 'cargo test', 'cargo clippy', custom command)",
          },
        },
        required: ["claim", "method"],
      },
      handler: async (args: { claim: string; method: string }) => {
        // Execute verification command
        const result = executeCommand(args.method, context.codebasePath);

        context.audit.log("verify_claim", {
          claim: args.claim,
          method: args.method,
          success: result.success,
        });

        return {
          success: result.success,
          claim: args.claim,
          method: args.method,
          output: result.output.slice(0, 2000), // Truncate to 2KB
          error: result.error,
          verified_at: Date.now(),
        };
      },
    },
    {
      name: "verify_all_tests",
      description: "Run all tests in the codebase (cargo test --all)",
      inputSchema: {
        type: "object",
        properties: {
          release: {
            type: "boolean",
            description: "Run tests in release mode (slower but more realistic)",
          },
        },
      },
      handler: async (args: { release?: boolean }) => {
        const command = args.release ? "cargo test --all --release" : "cargo test --all";

        const result = executeCommand(command, context.codebasePath, 300000); // 5 minute timeout

        // Parse output to extract test counts (if possible)
        const passedMatch = result.output.match(/test result: ok\. (\d+) passed/);
        const passed = passedMatch ? parseInt(passedMatch[1], 10) : null;

        context.audit.log("verify_all_tests", {
          release: args.release || false,
          success: result.success,
          passed,
        });

        return {
          success: result.success,
          command,
          passed,
          output: result.output.slice(-2000), // Last 2KB of output
          error: result.error,
          verified_at: Date.now(),
        };
      },
    },
    {
      name: "verify_clippy",
      description: "Run clippy (Rust linter) and return any warnings/errors",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const command = "cargo clippy --all-targets --all-features";

        const result = executeCommand(command, context.codebasePath, 120000); // 2 minute timeout

        // Parse warnings/errors
        const warningMatches = result.output.match(/warning: /g);
        const errorMatches = result.output.match(/error: /g);

        const warningCount = warningMatches ? warningMatches.length : 0;
        const errorCount = errorMatches ? errorMatches.length : 0;

        context.audit.log("verify_clippy", {
          success: result.success,
          warnings: warningCount,
          errors: errorCount,
        });

        return {
          success: result.success,
          command,
          warnings: warningCount,
          errors: errorCount,
          output: result.output.slice(-2000), // Last 2KB
          error: result.error,
          verified_at: Date.now(),
        };
      },
    },
  ];
}
