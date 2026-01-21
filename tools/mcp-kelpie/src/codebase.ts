/**
 * Codebase access tools - Direct access to grep, peek, read_section
 *
 * Wraps RLM Python environment's CodebaseContext for convenience.
 * TigerStyle: Subprocess isolation, explicit limits
 */

import { spawn } from "child_process";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface CodebaseContext {
  codebasePath: string;
  indexesPath: string;
  audit: AuditContext;
}

const CODEBASE_TIMEOUT_MS = 10000; // 10 seconds
const CODEBASE_OUTPUT_SIZE_BYTES_MAX = 100 * 1024; // 100KB

/**
 * Execute codebase operation via RLM subprocess
 */
async function executeCodebaseOp(
  codebasePath: string,
  indexesPath: string,
  code: string
): Promise<{ success: boolean; result?: any; error?: string }> {
  return new Promise((resolve) => {
    const rlmEnvPath = join(codebasePath, "tools", "rlm-env");

    const proc = spawn("python", ["-m", "rlm_env", "exec", "-"], {
      cwd: rlmEnvPath,
      env: {
        ...process.env,
        KELPIE_CODEBASE_PATH: codebasePath,
        KELPIE_INDEXES_PATH: indexesPath,
      },
      timeout: CODEBASE_TIMEOUT_MS,
    });

    let stdout = "";
    let stderr = "";

    proc.stdout.on("data", (data) => {
      stdout += data.toString();
      if (stdout.length > CODEBASE_OUTPUT_SIZE_BYTES_MAX) {
        proc.kill("SIGTERM");
        resolve({
          success: false,
          error: `Output size exceeded ${CODEBASE_OUTPUT_SIZE_BYTES_MAX} bytes`,
        });
      }
    });

    proc.stderr.on("data", (data) => {
      stderr += data.toString();
    });

    proc.stdin.write(code);
    proc.stdin.end();

    proc.on("close", () => {
      if (stdout.length > CODEBASE_OUTPUT_SIZE_BYTES_MAX) {
        return; // Already resolved
      }

      try {
        const result = JSON.parse(stdout);
        resolve({
          success: result.success,
          result: result.result,
          error: result.error,
        });
      } catch (parseError) {
        resolve({
          success: false,
          error: `Failed to parse output: ${parseError}\nStdout: ${stdout.slice(0, 500)}`,
        });
      }
    });

    proc.on("error", (error) => {
      resolve({
        success: false,
        error: `Subprocess error: ${error.message}`,
      });
    });

    setTimeout(() => {
      if (!proc.killed) {
        proc.kill("SIGTERM");
        resolve({
          success: false,
          error: `Timeout after ${CODEBASE_TIMEOUT_MS}ms`,
        });
      }
    }, CODEBASE_TIMEOUT_MS + 1000);
  });
}

/**
 * Create codebase access tools
 */
export function createCodebaseTools(
  context: CodebaseContext
): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "codebase_grep",
      description: "Search codebase for pattern (regex supported)",
      inputSchema: {
        type: "object",
        properties: {
          pattern: {
            type: "string",
            description: "Regex pattern to search for",
          },
          file_pattern: {
            type: "string",
            description: "Optional file glob pattern (e.g., '*.rs', 'src/**/*.rs')",
          },
          max_results: {
            type: "number",
            description: "Maximum results to return (default 50)",
          },
        },
        required: ["pattern"],
      },
      handler: async (args: { pattern: string; file_pattern?: string; max_results?: number }) => {
        const maxResults = args.max_results || 50;
        const filePattern = args.file_pattern ? `, file_pattern='${args.file_pattern}'` : "";

        const code = `
result = codebase.grep('${args.pattern.replace(/'/g, "\\'")}', max_results=${maxResults}${filePattern})
`;

        context.audit.log("codebase_grep", {
          pattern: args.pattern,
          file_pattern: args.file_pattern,
          max_results: maxResults,
        });

        return await executeCodebaseOp(context.codebasePath, context.indexesPath, code);
      },
    },
    {
      name: "codebase_peek",
      description: "Read lines from file around a line number",
      inputSchema: {
        type: "object",
        properties: {
          file_path: {
            type: "string",
            description: "Path to file (relative to codebase root)",
          },
          line: {
            type: "number",
            description: "Center line number",
          },
          context: {
            type: "number",
            description: "Number of context lines before/after (default 10)",
          },
        },
        required: ["file_path", "line"],
      },
      handler: async (args: { file_path: string; line: number; context?: number }) => {
        const contextLines = args.context || 10;

        const code = `
result = codebase.peek('${args.file_path.replace(/'/g, "\\'")}', ${args.line}, ${contextLines})
`;

        context.audit.log("codebase_peek", {
          file_path: args.file_path,
          line: args.line,
          context: contextLines,
        });

        return await executeCodebaseOp(context.codebasePath, context.indexesPath, code);
      },
    },
    {
      name: "codebase_read_section",
      description: "Read specific section (function, struct, impl block) from file",
      inputSchema: {
        type: "object",
        properties: {
          file_path: {
            type: "string",
            description: "Path to file (relative to codebase root)",
          },
          symbol: {
            type: "string",
            description: "Symbol name (function, struct, etc.)",
          },
        },
        required: ["file_path", "symbol"],
      },
      handler: async (args: { file_path: string; symbol: string }) => {
        const code = `
result = codebase.read_section('${args.file_path.replace(/'/g, "\\'")}', '${args.symbol.replace(/'/g, "\\'")}')
`;

        context.audit.log("codebase_read_section", {
          file_path: args.file_path,
          symbol: args.symbol,
        });

        return await executeCodebaseOp(context.codebasePath, context.indexesPath, code);
      },
    },
  ];
}
