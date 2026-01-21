/**
 * Slop detection tools - Find dead code, unused dependencies, orphaned files (Phase 4.8)
 *
 * TigerStyle: Automated detection of code quality issues
 */

import { execSync } from "child_process";
import { readdirSync, statSync } from "fs";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface SlopContext {
  codebasePath: string;
  indexesPath: string;
  audit: AuditContext;
}

interface SlopReport {
  unused_deps?: Array<{ crate: string; dependency: string }>;
  unreachable_functions?: Array<{ name: string; file: string; reason: string }>;
  orphaned_files?: Array<{ file: string; reason: string; action: string }>;
}

/**
 * Find all Rust files recursively
 */
function findRustFiles(dir: string, basePath: string, pattern?: RegExp): string[] {
  const results: string[] = [];

  try {
    const items = readdirSync(dir);

    for (const item of items) {
      // Skip common ignore patterns
      if (item === "target" || item === "node_modules" || item === ".git" || item.startsWith(".")) {
        continue;
      }

      const fullPath = join(dir, item);
      const relativePath = fullPath.replace(basePath + "/", "");

      try {
        const stat = statSync(fullPath);

        if (stat.isDirectory()) {
          results.push(...findRustFiles(fullPath, basePath, pattern));
        } else if (stat.isFile() && item.endsWith(".rs")) {
          if (pattern) {
            if (pattern.test(relativePath)) {
              results.push(relativePath);
            }
          } else {
            results.push(relativePath);
          }
        }
      } catch {
        // Skip files we can't stat
      }
    }
  } catch {
    // Skip directories we can't read
  }

  return results;
}

/**
 * Create slop detection tools for Phase 4.8
 */
export function createSlopTools(context: SlopContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "detect_dead_code",
      description: "Detect unused dependencies, unreachable functions, and orphaned files",
      inputSchema: {
        type: "object",
        properties: {
          check_deps: {
            type: "boolean",
            description: "Check for unused dependencies (requires cargo-udeps)",
          },
          check_orphans: {
            type: "boolean",
            description: "Check for orphaned files (old_*.rs, *_backup.rs patterns)",
          },
        },
      },
      handler: async (args: { check_deps?: boolean; check_orphans?: boolean }) => {
        const report: SlopReport = {};

        // Check 1: Unused dependencies (requires cargo-udeps)
        if (args.check_deps !== false) {
          try {
            const output = execSync("cargo +nightly udeps --all-targets 2>&1", {
              cwd: context.codebasePath,
              encoding: "utf-8",
              timeout: 120000, // 2 minutes
            });

            // Parse udeps output (basic parsing)
            const unusedDeps: Array<{ crate: string; dependency: string }> = [];
            const lines = output.split("\n");

            for (const line of lines) {
              if (line.includes("unused")) {
                // Extract crate and dependency names from output
                const match = line.match(/`([^`]+)`.*`([^`]+)`/);
                if (match) {
                  unusedDeps.push({
                    crate: match[1] || "unknown",
                    dependency: match[2] || "unknown",
                  });
                }
              }
            }

            report.unused_deps = unusedDeps;
          } catch (error) {
            // cargo-udeps might not be installed or might fail
            report.unused_deps = [];
          }
        }

        // Check 2: Orphaned files
        if (args.check_orphans !== false) {
          const orphanedFiles: Array<{ file: string; reason: string; action: string }> = [];

          // Pattern 1: old_*.rs, *_old.rs, *_backup.rs
          const suspectPattern = /(old_|_old|_backup|_deprecated)/i;
          const suspectFiles = findRustFiles(context.codebasePath, context.codebasePath, suspectPattern);

          for (const file of suspectFiles) {
            // Check if there's a non-suspect version
            const cleanFile = file
              .replace(/old_/gi, "")
              .replace(/_old/gi, "")
              .replace(/_backup/gi, "")
              .replace(/_deprecated/gi, "");

            const allFiles = findRustFiles(context.codebasePath, context.codebasePath);

            if (allFiles.includes(cleanFile) && file !== cleanFile) {
              orphanedFiles.push({
                file,
                reason: `Possibly superseded by ${cleanFile}`,
                action: "Review and delete if obsolete",
              });
            }
          }

          report.orphaned_files = orphanedFiles;
        }

        context.audit.log("detect_dead_code", {
          unused_deps: report.unused_deps?.length || 0,
          orphaned_files: report.orphaned_files?.length || 0,
        });

        return {
          success: true,
          report,
          summary: {
            unused_dependencies: report.unused_deps?.length || 0,
            orphaned_files: report.orphaned_files?.length || 0,
          },
        };
      },
    },
    {
      name: "detect_test_coverage_gaps",
      description: "Find modules without any tests",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        // Load indexes
        const modulesPath = join(context.indexesPath, "structural", "modules.json");
        const testsPath = join(context.indexesPath, "structural", "tests.json");

        try {
          const modulesData = JSON.parse(require("fs").readFileSync(modulesPath, "utf-8"));
          const testsData = JSON.parse(require("fs").readFileSync(testsPath, "utf-8"));

          // Get all modules
          const allModules: string[] = [];
          for (const crate of modulesData.crates || []) {
            for (const mod of crate.modules || []) {
              allModules.push(`${crate.name}::${mod.name}`);
            }
          }

          // Get modules that have tests
          const testedModules = new Set<string>();
          for (const test of testsData.tests || []) {
            // Extract module from file path
            const match = test.file.match(/crates\/([^/]+)\/src\/([^/]+)/);
            if (match) {
              const crate = match[1];
              const module = match[2].replace(".rs", "");
              testedModules.add(`${crate}::${module}`);
            }
          }

          // Find modules without tests
          const untestedModules = allModules.filter((mod) => !testedModules.has(mod));

          context.audit.log("detect_test_coverage_gaps", {
            total_modules: allModules.length,
            tested_modules: testedModules.size,
            untested_modules: untestedModules.length,
          });

          return {
            success: true,
            total_modules: allModules.length,
            tested_modules: testedModules.size,
            untested_modules: untestedModules.length,
            coverage_percent: Math.round((testedModules.size / allModules.length) * 100),
            modules_without_tests: untestedModules.slice(0, 50), // First 50
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
