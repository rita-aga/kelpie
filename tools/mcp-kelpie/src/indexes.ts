/**
 * Index query tools
 *
 * TigerStyle: Index queries check freshness before returning results
 */

import { readFileSync, existsSync, statSync } from "fs";
import { join } from "path";
import { execSync } from "child_process";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface IndexContext {
  indexesPath: string;
  codebasePath: string;
  audit: AuditContext;
}

interface Index {
  [key: string]: any;
}

/**
 * Load index file
 * TigerStyle: Validate existence and parse safely
 */
function loadIndex(indexesPath: string, indexName: string): Index {
  const indexPath = join(indexesPath, "structural", `${indexName}.json`);

  if (!existsSync(indexPath)) {
    throw new Error(`Index not found: ${indexName} (expected at ${indexPath})`);
  }

  try {
    const content = readFileSync(indexPath, "utf-8");
    return JSON.parse(content);
  } catch (error) {
    throw new Error(`Failed to parse index ${indexName}: ${error}`);
  }
}

/**
 * Get current git HEAD SHA
 * TigerStyle: Explicit error handling
 */
function getCurrentGitSha(codebasePath: string): string | null {
  try {
    const sha = execSync("git rev-parse HEAD", {
      cwd: codebasePath,
      encoding: "utf-8",
    }).trim();
    return sha;
  } catch (error) {
    // Not in a git repo or git not available
    return null;
  }
}

/**
 * Check index freshness
 * TigerStyle: Hard control - warn if index is stale
 *
 * CRITICAL: Compare git SHAs first (plan requirement)
 * - If git SHA changed since index build → STALE
 * - If git SHA unavailable, fall back to time-based check
 * - If >1 hour old → WARNING (but not necessarily stale if no commits)
 */
function checkFreshness(indexesPath: string, codebasePath: string): { fresh: boolean; message?: string; git_sha_mismatch?: boolean } {
  const freshnessPath = join(indexesPath, "meta", "freshness.json");

  if (!existsSync(freshnessPath)) {
    return { fresh: false, message: "Freshness tracking not found" };
  }

  try {
    const freshness = JSON.parse(readFileSync(freshnessPath, "utf-8"));

    // CRITICAL: Compare git SHAs (plan requirement)
    const currentSha = getCurrentGitSha(codebasePath);
    if (currentSha !== null && freshness.git_sha) {
      if (currentSha !== freshness.git_sha) {
        return {
          fresh: false,
          message: `Index stale: git SHA changed (index: ${freshness.git_sha.slice(0, 8)}, current: ${currentSha.slice(0, 8)}). Run index_refresh.`,
          git_sha_mismatch: true,
        };
      }
    }

    // Time-based check as secondary warning (not a hard failure)
    const indexAge = Date.now() - freshness.built_at;
    const ageMinutes = Math.floor(indexAge / 60000);

    if (ageMinutes > 60) {
      return {
        fresh: false,
        message: `Indexes are ${ageMinutes} minutes old (built at ${new Date(freshness.built_at).toISOString()}). Consider refreshing.`,
      };
    }

    return { fresh: true };
  } catch (error) {
    return { fresh: false, message: `Failed to check freshness: ${error}` };
  }
}

/**
 * Create index query tools
 * Phase 4.3: index_symbols, index_tests, index_modules, index_deps, index_constraints
 */
export function createIndexTools(context: IndexContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "index_symbols",
      description: "Find symbols matching a pattern across the codebase",
      inputSchema: {
        type: "object",
        properties: {
          pattern: {
            type: "string",
            description: "Pattern to match (regex or simple string)",
          },
          kind: {
            type: "string",
            description: "Optional: filter by symbol kind (fn, struct, enum, trait, etc.)",
          },
        },
        required: ["pattern"],
      },
      handler: async (args: { pattern: string; kind?: string }) => {
        const freshness = checkFreshness(context.indexesPath, context.codebasePath);
        const symbols = loadIndex(context.indexesPath, "symbols");

        const matches: Array<{
          file: string;
          name: string;
          kind: string;
          visibility: string;
          line: number;
        }> = [];

        const regex = new RegExp(args.pattern, "i");

        for (const [file, fileData] of Object.entries(symbols.files)) {
          const data = fileData as { symbols: Array<any> };
          for (const symbol of data.symbols) {
            const matchesPattern = regex.test(symbol.name);
            const matchesKind = !args.kind || symbol.kind === args.kind;

            if (matchesPattern && matchesKind) {
              matches.push({
                file,
                name: symbol.name,
                kind: symbol.kind,
                visibility: symbol.visibility,
                line: symbol.line || 0,
              });
            }
          }
        }

        context.audit.log("index_symbols", {
          pattern: args.pattern,
          matches: matches.length,
        });

        return {
          success: true,
          matches,
          count: matches.length,
          freshness,
        };
      },
    },
    {
      name: "index_tests",
      description: "Find tests by topic or type",
      inputSchema: {
        type: "object",
        properties: {
          topic: {
            type: "string",
            description: "Topic to search for (e.g., 'storage', 'actor')",
          },
          type: {
            type: "string",
            description: "Test type filter (unit, dst, integration, chaos)",
          },
        },
      },
      handler: async (args: { topic?: string; type?: string }) => {
        const freshness = checkFreshness(context.indexesPath, context.codebasePath);
        const tests = loadIndex(context.indexesPath, "tests");

        let matches = tests.tests || [];

        // Filter by topic
        if (args.topic) {
          matches = matches.filter((t: any) => t.topics && t.topics.includes(args.topic));
        }

        // Filter by type
        if (args.type) {
          matches = matches.filter((t: any) => t.type === args.type);
        }

        context.audit.log("index_tests", {
          topic: args.topic,
          type: args.type,
          matches: matches.length,
        });

        return {
          success: true,
          tests: matches,
          count: matches.length,
          freshness,
        };
      },
    },
    {
      name: "index_modules",
      description: "Get module hierarchy information",
      inputSchema: {
        type: "object",
        properties: {
          crate: {
            type: "string",
            description: "Optional: filter by crate name",
          },
        },
      },
      handler: async (args: { crate?: string }) => {
        const freshness = checkFreshness(context.indexesPath, context.codebasePath);
        const modules = loadIndex(context.indexesPath, "modules");

        let crates = modules.crates || [];

        // Filter by crate if specified
        if (args.crate) {
          crates = crates.filter((c: any) => c.name === args.crate);
        }

        context.audit.log("index_modules", {
          crate: args.crate,
          crates_count: crates.length,
        });

        return {
          success: true,
          crates,
          count: crates.length,
          freshness,
        };
      },
    },
    {
      name: "index_deps",
      description: "Get dependency graph information",
      inputSchema: {
        type: "object",
        properties: {
          crate: {
            type: "string",
            description: "Optional: get dependencies for specific crate",
          },
        },
      },
      handler: async (args: { crate?: string }) => {
        const freshness = checkFreshness(context.indexesPath, context.codebasePath);
        const deps = loadIndex(context.indexesPath, "dependencies");

        let edges = deps.edges || [];

        // Filter by crate if specified
        if (args.crate) {
          edges = edges.filter((e: any) => e.from === args.crate);
        }

        context.audit.log("index_deps", {
          crate: args.crate,
          edges_count: edges.length,
        });

        return {
          success: true,
          nodes: deps.nodes || [],
          edges,
          freshness,
        };
      },
    },
    {
      name: "index_status",
      description: "Get status of all indexes (freshness, file counts)",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const freshness = checkFreshness(context.indexesPath, context.codebasePath);
        const status: Record<string, any> = { freshness };

        // Check each index
        const indexes = ["symbols", "tests", "modules", "dependencies"];
        for (const indexName of indexes) {
          try {
            const index = loadIndex(context.indexesPath, indexName);
            const indexPath = join(context.indexesPath, "structural", `${indexName}.json`);
            const stats = statSync(indexPath);

            status[indexName] = {
              exists: true,
              size_bytes: stats.size,
              modified_at: stats.mtimeMs,
              git_sha: index.git_sha || "unknown",
              built_at: index.built_at || null,
            };
          } catch (error) {
            status[indexName] = {
              exists: false,
              error: error instanceof Error ? error.message : String(error),
            };
          }
        }

        context.audit.log("index_status", {});

        return {
          success: true,
          status,
        };
      },
    },
    {
      name: "index_refresh",
      description: "Rebuild indexes by running kelpie-indexer (Phase 4.5)",
      inputSchema: {
        type: "object",
        properties: {
          scope: {
            type: "string",
            description: "Optional: which index to rebuild (symbols, tests, modules, dependencies, all)",
            enum: ["symbols", "tests", "modules", "dependencies", "all"],
          },
        },
      },
      handler: async (args: { scope?: string }) => {
        const scope = args.scope || "all";
        const indexes = scope === "all" ? ["symbols", "dependencies", "tests", "modules"] : [scope];

        const results: Array<{ index: string; success: boolean; output?: string; error?: string }> = [];

        for (const indexName of indexes) {
          try {
            const command = `cargo run -p kelpie-indexer -- ${indexName}`;
            const output = execSync(command, {
              cwd: context.codebasePath,
              encoding: "utf-8",
              timeout: 120000, // 2 minute timeout per index
            });

            results.push({
              index: indexName,
              success: true,
              output: output.slice(-500), // Last 500 chars
            });
          } catch (error: any) {
            results.push({
              index: indexName,
              success: false,
              error: error.message || String(error),
            });
          }
        }

        const successCount = results.filter((r) => r.success).length;
        const failedCount = results.length - successCount;

        context.audit.log("index_refresh", {
          scope,
          indexes_rebuilt: successCount,
          failed: failedCount,
        });

        return {
          success: failedCount === 0,
          scope,
          results,
          rebuilt: successCount,
          failed: failedCount,
        };
      },
    },
    {
      name: "index_validate",
      description: "Cross-validate indexes for consistency (Phase 4.5)",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const issues: Array<{ type: string; message: string }> = [];

        try {
          // Load all indexes
          const symbols = loadIndex(context.indexesPath, "symbols");
          const tests = loadIndex(context.indexesPath, "tests");
          const modules = loadIndex(context.indexesPath, "modules");
          const deps = loadIndex(context.indexesPath, "dependencies");

          // Validation 1: Check git SHA consistency
          const gitShas = [symbols.git_sha, tests.git_sha, modules.git_sha, deps.git_sha];
          const uniqueShas = [...new Set(gitShas.filter((s) => s))];

          if (uniqueShas.length > 1) {
            issues.push({
              type: "git_sha_mismatch",
              message: `Indexes have different git SHAs: ${uniqueShas.join(", ")}. Rebuild needed.`,
            });
          }

          // Validation 2: Check that test files exist in symbols index
          const symbolFiles = new Set(Object.keys(symbols.files || {}));
          const testFiles = (tests.tests || []).map((t: any) => t.file as string);
          const testFilesSet = new Set<string>(testFiles);

          let missingTestFiles = 0;
          for (const testFile of testFilesSet) {
            if (!symbolFiles.has(testFile)) {
              missingTestFiles++;
            }
          }

          if (missingTestFiles > 0) {
            issues.push({
              type: "missing_test_files",
              message: `${missingTestFiles} test files not found in symbols index`,
            });
          }

          // Validation 3: Check module count consistency
          const moduleCount = (modules.crates || []).reduce((sum: number, c: any) => sum + c.modules.length, 0);
          if (moduleCount === 0 && Object.keys(symbols.files || {}).length > 0) {
            issues.push({
              type: "no_modules",
              message: "No modules found but symbols index has files",
            });
          }

          // Validation 4: Check dependency node count vs crate count
          const depNodeCount = (deps.nodes || []).length;
          const crateCount = (modules.crates || []).length;
          if (Math.abs(depNodeCount - crateCount) > 2) {
            issues.push({
              type: "dep_crate_mismatch",
              message: `Dependency nodes (${depNodeCount}) and crates (${crateCount}) differ significantly`,
            });
          }

          context.audit.log("index_validate", {
            issues_found: issues.length,
          });

          return {
            success: issues.length === 0,
            issues,
            message: issues.length === 0 ? "All indexes are consistent" : `Found ${issues.length} consistency issues`,
          };
        } catch (error) {
          return {
            success: false,
            error: error instanceof Error ? error.message : String(error),
          };
        }
      },
    },
  ];
}
