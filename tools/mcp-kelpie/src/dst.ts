/**
 * DST (Deterministic Simulation Testing) coverage tools - Phase 4.9
 *
 * Verifies simulation-first development compliance from .vision/CONSTRAINTS.md
 * TigerStyle: Hard enforcement of DST coverage requirements
 */

import { execSync } from "child_process";
import { readFileSync, existsSync } from "fs";
import { join } from "path";
import { Tool } from "@modelcontextprotocol/sdk/types.js";
import { AuditContext } from "./audit.js";

export interface DstContext {
  codebasePath: string;
  indexesPath: string;
  audit: AuditContext;
}

interface DstCoverageReport {
  critical_paths: Array<{
    name: string;
    has_dst_test: boolean;
    test_files?: string[];
    missing_reason?: string;
  }>;
  total_dst_tests: number;
  coverage_percentage: number;
}

interface DstGapReport {
  modules_without_dst: Array<{
    module: string;
    crate: string;
    reason: string;
  }>;
  features_without_dst: Array<{
    feature: string;
    file: string;
    reason: string;
  }>;
}

/**
 * Critical paths that MUST have DST coverage per CONSTRAINTS.md
 */
const CRITICAL_PATHS = [
  {
    name: "actor activation/deactivation",
    search_patterns: ["actor.*activate", "actor.*deactivate", "spawn.*actor"],
  },
  {
    name: "state persistence and recovery",
    search_patterns: ["state.*persist", "state.*recover", "state.*save"],
  },
  {
    name: "cross-actor invocation",
    search_patterns: ["invoke.*actor", "call.*actor", "send.*message"],
  },
  {
    name: "failure detection and recovery",
    search_patterns: ["fail.*detect", "recover.*fail", "health.*check"],
  },
  {
    name: "migration correctness",
    search_patterns: ["migrate.*actor", "relocate.*actor", "transfer.*state"],
  },
  {
    name: "memory tier operations",
    search_patterns: ["memory.*tier", "core.*memory", "working.*memory", "archival.*memory"],
  },
  {
    name: "tool execution with sandbox",
    search_patterns: ["tool.*exec", "sandbox.*run", "restricted.*exec"],
  },
];

/**
 * Check if critical path has DST coverage
 */
function checkCriticalPathCoverage(codebasePath: string, criticalPath: typeof CRITICAL_PATHS[0]): {
  has_dst_test: boolean;
  test_files?: string[];
  missing_reason?: string;
} {
  const testFiles: string[] = [];

  try {
    for (const pattern of criticalPath.search_patterns) {
      const output = execSync(`git grep -l '${pattern}' -- '*_dst.rs' || true`, {
        cwd: codebasePath,
        encoding: "utf-8",
        timeout: 5000,
      });

      if (output.trim()) {
        const files = output.trim().split("\n");
        testFiles.push(...files);
      }
    }

    if (testFiles.length > 0) {
      return {
        has_dst_test: true,
        test_files: [...new Set(testFiles)], // Deduplicate
      };
    } else {
      return {
        has_dst_test: false,
        missing_reason: "No DST test files found matching patterns",
      };
    }
  } catch (error) {
    return {
      has_dst_test: false,
      missing_reason: `Failed to check coverage: ${error}`,
    };
  }
}

/**
 * Count total DST tests
 */
function countDstTests(codebasePath: string): number {
  try {
    const output = execSync(`git ls-files '*_dst.rs' | wc -l`, {
      cwd: codebasePath,
      encoding: "utf-8",
      timeout: 5000,
    });

    return parseInt(output.trim(), 10);
  } catch {
    return 0;
  }
}

/**
 * Find modules without DST tests
 */
function findModulesWithoutDst(codebasePath: string, indexesPath: string): Array<{
  module: string;
  crate: string;
  reason: string;
}> {
  const gaps: Array<{ module: string; crate: string; reason: string }> = [];

  try {
    const modulesPath = join(indexesPath, "structural", "modules.json");

    if (!existsSync(modulesPath)) {
      gaps.push({
        module: "N/A",
        crate: "N/A",
        reason: "modules.json not found - indexes need rebuilding",
      });
      return gaps;
    }

    const modulesData = JSON.parse(readFileSync(modulesPath, "utf-8"));

    for (const crate of modulesData.crates || []) {
      for (const mod of crate.modules || []) {
        // Check if this module has DST tests
        const moduleName = mod.name || "unknown";
        const crateName = crate.name || "unknown";

        try {
          const output = execSync(`git ls-files 'crates/${crateName}/**/*${moduleName}*_dst.rs' | wc -l`, {
            cwd: codebasePath,
            encoding: "utf-8",
            timeout: 3000,
          });

          const testCount = parseInt(output.trim(), 10);

          if (testCount === 0) {
            gaps.push({
              module: moduleName,
              crate: crateName,
              reason: "No DST test files found",
            });
          }
        } catch {
          // Skip if check fails
        }
      }
    }
  } catch (error) {
    gaps.push({
      module: "N/A",
      crate: "N/A",
      reason: `Failed to analyze modules: ${error}`,
    });
  }

  return gaps.slice(0, 20); // Limit to first 20
}

/**
 * Create DST coverage checking tools for Phase 4.9
 */
export function createDstTools(context: DstContext): Array<Tool & { handler: (args: any) => Promise<any> }> {
  return [
    {
      name: "dst_coverage_check",
      description: "Check DST coverage for critical paths (simulation-first compliance)",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const report: DstCoverageReport = {
          critical_paths: [],
          total_dst_tests: 0,
          coverage_percentage: 0,
        };

        // Check each critical path
        for (const path of CRITICAL_PATHS) {
          const coverage = checkCriticalPathCoverage(context.codebasePath, path);
          report.critical_paths.push({
            name: path.name,
            has_dst_test: coverage.has_dst_test,
            test_files: coverage.test_files,
            missing_reason: coverage.missing_reason,
          });
        }

        // Count total DST tests
        report.total_dst_tests = countDstTests(context.codebasePath);

        // Calculate coverage percentage
        const covered = report.critical_paths.filter((p) => p.has_dst_test).length;
        report.coverage_percentage = Math.round((covered / CRITICAL_PATHS.length) * 100);

        context.audit.log("dst_coverage_check", {
          total_critical_paths: CRITICAL_PATHS.length,
          paths_covered: covered,
          coverage_percentage: report.coverage_percentage,
        });

        return {
          success: report.coverage_percentage === 100,
          report,
          message:
            report.coverage_percentage === 100
              ? "All critical paths have DST coverage"
              : `${CRITICAL_PATHS.length - covered} critical paths missing DST tests`,
        };
      },
    },
    {
      name: "dst_gaps_report",
      description: "Generate detailed report of DST coverage gaps (modules and features without tests)",
      inputSchema: {
        type: "object",
        properties: {},
      },
      handler: async () => {
        const report: DstGapReport = {
          modules_without_dst: [],
          features_without_dst: [],
        };

        // Find modules without DST tests
        report.modules_without_dst = findModulesWithoutDst(context.codebasePath, context.indexesPath);

        // Find features without DST tests (basic heuristic)
        try {
          // Look for pub fn in non-test files
          const output = execSync(
            `git grep -l 'pub fn' -- 'crates/*/src/*.rs' ':(exclude)*test*.rs' | head -20`,
            {
              cwd: context.codebasePath,
              encoding: "utf-8",
              timeout: 10000,
            }
          );

          if (output.trim()) {
            const files = output.trim().split("\n");

            for (const file of files) {
              // Check if this file has corresponding DST test
              const baseName = file.replace(/\.rs$/, "");
              const dstTestFile = `${baseName}_dst.rs`;

              try {
                const testExists = execSync(`git ls-files '${dstTestFile}' | wc -l`, {
                  cwd: context.codebasePath,
                  encoding: "utf-8",
                  timeout: 2000,
                });

                if (parseInt(testExists.trim(), 10) === 0) {
                  report.features_without_dst.push({
                    feature: file,
                    file,
                    reason: "No corresponding DST test file found",
                  });
                }
              } catch {
                // Skip if check fails
              }
            }
          }
        } catch {
          // Skip if feature check fails
        }

        context.audit.log("dst_gaps_report", {
          modules_without_dst: report.modules_without_dst.length,
          features_without_dst: report.features_without_dst.length,
        });

        return {
          success: true,
          report,
          summary: {
            modules_without_dst: report.modules_without_dst.length,
            features_without_dst: report.features_without_dst.length,
            total_gaps: report.modules_without_dst.length + report.features_without_dst.length,
          },
        };
      },
    },
    {
      name: "harness_check",
      description: "Check if DST harness supports required fault types for a feature",
      inputSchema: {
        type: "object",
        properties: {
          fault_types: {
            type: "array",
            description: "List of fault types needed (e.g., StorageWriteFail, NetworkPartition, etc.)",
            items: {
              type: "string",
            },
          },
        },
        required: ["fault_types"],
      },
      handler: async (args: { fault_types: string[] }) => {
        // Known fault types in kelpie-dst per CONSTRAINTS.md
        const supportedFaults = new Set([
          // Storage faults
          "StorageWriteFail",
          "StorageReadFail",
          "StorageCorruption",
          "StorageLatency",
          "DiskFull",
          // Crash faults
          "CrashBeforeWrite",
          "CrashAfterWrite",
          "CrashDuringTransaction",
          // Network faults
          "NetworkPartition",
          "NetworkDelay",
          "NetworkPacketLoss",
          "NetworkMessageReorder",
          // Time faults
          "ClockSkew",
          "ClockJump",
          // Resource faults
          "OutOfMemory",
          "CPUStarvation",
        ]);

        const results: Array<{
          fault_type: string;
          supported: boolean;
          category?: string;
          needs_extension?: boolean;
        }> = [];

        for (const faultType of args.fault_types) {
          const isSupported = supportedFaults.has(faultType);

          // Determine category
          let category = "unknown";
          if (faultType.toLowerCase().includes("storage") || faultType.toLowerCase().includes("disk")) {
            category = "storage";
          } else if (faultType.toLowerCase().includes("crash")) {
            category = "crash";
          } else if (faultType.toLowerCase().includes("network")) {
            category = "network";
          } else if (faultType.toLowerCase().includes("clock") || faultType.toLowerCase().includes("time")) {
            category = "time";
          } else if (
            faultType.toLowerCase().includes("memory") ||
            faultType.toLowerCase().includes("cpu") ||
            faultType.toLowerCase().includes("resource")
          ) {
            category = "resource";
          }

          results.push({
            fault_type: faultType,
            supported: isSupported,
            category: isSupported ? category : undefined,
            needs_extension: !isSupported,
          });
        }

        const allSupported = results.every((r) => r.supported);
        const unsupportedFaults = results.filter((r) => !r.supported);

        context.audit.log("harness_check", {
          fault_types_requested: args.fault_types.length,
          all_supported: allSupported,
          unsupported_count: unsupportedFaults.length,
        });

        return {
          success: allSupported,
          results,
          summary: {
            total_requested: args.fault_types.length,
            supported: results.filter((r) => r.supported).length,
            unsupported: unsupportedFaults.length,
          },
          message: allSupported
            ? "All requested fault types are supported"
            : `${unsupportedFaults.length} fault types need harness extension: ${unsupportedFaults.map((f) => f.fault_type).join(", ")}`,
          next_steps: allSupported ? "Proceed with feature implementation" : "STOP - Extend harness FIRST to support missing faults",
        };
      },
    },
  ];
}
