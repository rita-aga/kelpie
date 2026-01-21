/**
 * RLM Integration Smoke Tests
 *
 * These tests actually invoke the RLM Python subprocess to verify the CLI interface works
 */

import { describe, it, expect } from "vitest";
import { createRlmTools } from "../src/rlm.js";
import { createCodebaseTools } from "../src/codebase.js";
import { AuditContext } from "../src/audit.js";
import { existsSync } from "fs";
import { join } from "path";

// Mock audit context
const createMockAudit = (): AuditContext => ({
  log: () => {},
});

// Check if we're in the correct repository structure
const codebasePath = process.cwd().includes("tools/mcp-kelpie")
  ? join(process.cwd(), "../..")
  : process.cwd();

const indexesPath = join(codebasePath, ".kelpie-index");
const rlmEnvPath = join(codebasePath, "tools", "rlm-env");

// Skip tests if RLM environment is not available
const shouldRunIntegrationTests = existsSync(rlmEnvPath) && existsSync(join(rlmEnvPath, "rlm_env", "__main__.py"));

describe.skipIf(!shouldRunIntegrationTests)("RLM Integration Smoke Tests", () => {
  const context = {
    codebasePath,
    indexesPath,
    audit: createMockAudit(),
  };

  it("should execute simple Python code via rlm_execute", async () => {
    const tools = createRlmTools(context);
    const rlmExecute = tools.find((t) => t.name === "rlm_execute");

    expect(rlmExecute).toBeDefined();

    const result = await (rlmExecute as any).handler({
      code: "result = 2 + 2",
    });

    expect(result.success).toBe(true);
    expect(result.result).toBe(4);
  }, 15000); // 15s timeout for subprocess

  it("should handle errors in rlm_execute", async () => {
    const tools = createRlmTools(context);
    const rlmExecute = tools.find((t) => t.name === "rlm_execute");

    const result = await (rlmExecute as any).handler({
      code: "result = 1 / 0",
    });

    expect(result.success).toBe(false);
    expect(result.error).toBeDefined();
    expect(result.error).toContain("ZeroDivisionError");
  }, 15000);

  it("should execute codebase_grep if indexes exist", async () => {
    // Only run if indexes directory exists
    if (!existsSync(indexesPath)) {
      console.log("Skipping codebase_grep test - indexes not found");
      return;
    }

    const tools = createCodebaseTools(context);
    const codebaseGrep = tools.find((t) => t.name === "codebase_grep");

    expect(codebaseGrep).toBeDefined();

    // Search for a common pattern that should exist
    const result = await (codebaseGrep as any).handler({
      pattern: "pub fn",
      max_results: 5,
    });

    expect(result.success).toBe(true);
    expect(result.result).toBeDefined();
  }, 15000);

  it("should reject empty code in rlm_execute", async () => {
    const tools = createRlmTools(context);
    const rlmExecute = tools.find((t) => t.name === "rlm_execute");

    const result = await (rlmExecute as any).handler({
      code: "",
    });

    expect(result.success).toBe(false);
    expect(result.error).toContain("empty");
  }, 15000);

  it("should enforce size limits in rlm_execute", async () => {
    const tools = createRlmTools(context);
    const rlmExecute = tools.find((t) => t.name === "rlm_execute");

    // Create code larger than 50KB
    const largeCode = "x = " + "'a' * 60000";

    const result = await (rlmExecute as any).handler({
      code: largeCode,
    });

    expect(result.success).toBe(false);
    expect(result.error).toContain("exceeds maximum size");
  }, 15000);
});

describe("RLM Tool Registration (Always Run)", () => {
  const context = {
    codebasePath: "/tmp",
    indexesPath: "/tmp/.kelpie-index",
    audit: createMockAudit(),
  };

  it("should register rlm_execute and rlm_map_reduce", () => {
    const tools = createRlmTools(context);
    expect(tools).toHaveLength(2);
    expect(tools.map((t) => t.name)).toContain("rlm_execute");
    expect(tools.map((t) => t.name)).toContain("rlm_map_reduce");
  });

  it("should register codebase tools", () => {
    const tools = createCodebaseTools(context);
    expect(tools).toHaveLength(3);
    expect(tools.map((t) => t.name)).toContain("codebase_grep");
    expect(tools.map((t) => t.name)).toContain("codebase_peek");
    expect(tools.map((t) => t.name)).toContain("codebase_read_section");
  });
});
