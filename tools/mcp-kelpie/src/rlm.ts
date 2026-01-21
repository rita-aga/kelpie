/**
 * RLM (Restricted Language Model) execution tools - Phase 4.7
 *
 * Integrates with tools/rlm-env/ Python package for sandboxed code execution.
 * TigerStyle: Subprocess isolation, timeouts, output limits
 */

import { spawn } from "child_process";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface RlmContext {
  codebasePath: string;
  indexesPath: string;
  audit: AuditContext;
}

// TigerStyle: Explicit constants with units
const RLM_EXECUTION_TIMEOUT_MS = 30000; // 30 seconds
const RLM_OUTPUT_SIZE_BYTES_MAX = 100 * 1024; // 100KB

interface RlmExecutionResult {
  success: boolean;
  result?: any;
  error?: string;
  execution_log?: string[];
  output_truncated?: boolean;
}

/**
 * Execute code in RLM sandbox via subprocess
 *
 * TigerStyle: Subprocess isolation, explicit timeouts
 */
async function executeRlmCode(
  codebasePath: string,
  indexesPath: string,
  code: string
): Promise<RlmExecutionResult> {
  return new Promise((resolve) => {
    // TigerStyle: Explicit path construction
    const rlmEnvPath = join(codebasePath, "tools", "rlm-env");

    // Spawn Python subprocess
    const proc = spawn("python", ["-m", "rlm_env", "exec", "-"], {
      cwd: rlmEnvPath,
      env: {
        ...process.env,
        KELPIE_CODEBASE_PATH: codebasePath,
        KELPIE_INDEXES_PATH: indexesPath,
      },
      timeout: RLM_EXECUTION_TIMEOUT_MS,
    });

    let stdout = "";
    let stderr = "";

    // TigerStyle: Enforce output size limit
    proc.stdout.on("data", (data) => {
      stdout += data.toString();
      if (stdout.length > RLM_OUTPUT_SIZE_BYTES_MAX) {
        proc.kill("SIGTERM");
        resolve({
          success: false,
          error: `Output size exceeded ${RLM_OUTPUT_SIZE_BYTES_MAX} bytes`,
          output_truncated: true,
        });
      }
    });

    proc.stderr.on("data", (data) => {
      stderr += data.toString();
      if (stderr.length > RLM_OUTPUT_SIZE_BYTES_MAX) {
        proc.kill("SIGTERM");
      }
    });

    // Send code to stdin
    proc.stdin.write(code);
    proc.stdin.end();

    // Handle completion
    proc.on("close", () => {
      if (stdout.length > RLM_OUTPUT_SIZE_BYTES_MAX || stderr.length > RLM_OUTPUT_SIZE_BYTES_MAX) {
        return; // Already resolved with truncation error
      }

      // Parse JSON result
      try {
        const result = JSON.parse(stdout);
        resolve({
          success: result.success,
          result: result.result,
          error: result.error,
          execution_log: result.execution_log,
        });
      } catch (parseError) {
        resolve({
          success: false,
          error: `Failed to parse RLM output: ${parseError}\nStdout: ${stdout.slice(0, 500)}\nStderr: ${stderr.slice(0, 500)}`,
        });
      }
    });

    // Handle timeout
    proc.on("error", (error) => {
      resolve({
        success: false,
        error: `RLM subprocess error: ${error.message}`,
      });
    });

    // TigerStyle: Explicit timeout handling
    setTimeout(() => {
      if (!proc.killed) {
        proc.kill("SIGTERM");
        resolve({
          success: false,
          error: `Execution timeout after ${RLM_EXECUTION_TIMEOUT_MS}ms`,
        });
      }
    }, RLM_EXECUTION_TIMEOUT_MS + 1000); // Grace period
  });
}

/**
 * Create RLM execution tools for Phase 4.7
 */
export function createRlmTools(context: RlmContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "rlm_execute",
      description: "Execute code in RLM (Restricted Language Model) sandbox with codebase access",
      inputSchema: {
        type: "object",
        properties: {
          code: {
            type: "string",
            description:
              "Python code to execute in sandbox. Has access to codebase.grep(), codebase.peek(), indexes, etc.",
          },
        },
        required: ["code"],
      },
      handler: async (args: { code: string }) => {
        // TigerStyle: Input validation
        if (!args.code || args.code.trim().length === 0) {
          return {
            success: false,
            error: "Code cannot be empty",
          };
        }

        if (args.code.length > 50000) {
          return {
            success: false,
            error: "Code exceeds maximum size (50KB)",
          };
        }

        context.audit.log("rlm_execute", {
          code_length: args.code.length,
        });

        const result = await executeRlmCode(context.codebasePath, context.indexesPath, args.code);

        context.audit.log("rlm_execute_result", {
          success: result.success,
          has_result: !!result.result,
          error: result.error ? result.error.slice(0, 200) : undefined,
        });

        return result;
      },
    },
    {
      name: "rlm_map_reduce",
      description: "Execute map-reduce pattern in RLM sandbox (partition + parallel map + reduce)",
      inputSchema: {
        type: "object",
        properties: {
          map_code: {
            type: "string",
            description: "Map function code (receives partition as input)",
          },
          reduce_code: {
            type: "string",
            description: "Reduce function code (receives list of map results)",
          },
          partitions: {
            type: "number",
            description: "Number of partitions (1-10)",
          },
        },
        required: ["map_code", "reduce_code", "partitions"],
      },
      handler: async (args: { map_code: string; reduce_code: string; partitions: number }) => {
        // TigerStyle: Input validation
        if (!args.map_code || !args.reduce_code) {
          return {
            success: false,
            error: "Map and reduce code required",
          };
        }

        if (args.partitions < 1 || args.partitions > 10) {
          return {
            success: false,
            error: "Partitions must be between 1 and 10",
          };
        }

        // Build map-reduce wrapper code
        const wrapperCode = `
# Map-reduce execution
map_fn = ${args.map_code}
reduce_fn = ${args.reduce_code}

# Execute map phase
map_results = []
for i in range(${args.partitions}):
    partition_result = map_fn(i)
    map_results.append(partition_result)

# Execute reduce phase
result = reduce_fn(map_results)
`;

        context.audit.log("rlm_map_reduce", {
          map_code_length: args.map_code.length,
          reduce_code_length: args.reduce_code.length,
          partitions: args.partitions,
        });

        const result = await executeRlmCode(context.codebasePath, context.indexesPath, wrapperCode);

        context.audit.log("rlm_map_reduce_result", {
          success: result.success,
          has_result: !!result.result,
        });

        return result;
      },
    },
  ];
}
