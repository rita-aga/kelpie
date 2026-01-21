/**
 * Index query tools
 *
 * TigerStyle: Index queries check freshness before returning results
 */

import { readFileSync, existsSync, statSync } from "fs";
import { join } from "path";
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
 * Check index freshness
 * TigerStyle: Hard control - warn if index is stale
 */
function checkFreshness(indexesPath: string): { fresh: boolean; message?: string } {
  const freshnessPath = join(indexesPath, "meta", "freshness.json");

  if (!existsSync(freshnessPath)) {
    return { fresh: false, message: "Freshness tracking not found" };
  }

  try {
    const freshness = JSON.parse(readFileSync(freshnessPath, "utf-8"));
    const indexAge = Date.now() - freshness.built_at;
    const ageMinutes = Math.floor(indexAge / 60000);

    // Warn if older than 1 hour
    if (ageMinutes > 60) {
      return {
        fresh: false,
        message: `Indexes are ${ageMinutes} minutes old (built at ${new Date(freshness.built_at).toISOString()})`,
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
        const freshness = checkFreshness(context.indexesPath);
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
        const freshness = checkFreshness(context.indexesPath);
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
        const freshness = checkFreshness(context.indexesPath);
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
        const freshness = checkFreshness(context.indexesPath);
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
        const freshness = checkFreshness(context.indexesPath);
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
  ];
}
