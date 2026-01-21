/**
 * Phase 8.2: MCP Tool Integration Test (Simplified)
 *
 * This test verifies that MCP tools work correctly with existing indexes.
 * Tests the integration between different tool categories without requiring
 * full index rebuilds.
 *
 * TigerStyle: Each step has explicit assertions
 */

import { describe, it, expect, beforeAll } from "vitest";
import { createIndexTools } from "../src/indexes.js";
import { createStateTools } from "../src/state.js";
import { existsSync, mkdirSync } from "fs";
import { join } from "path";

// Mock audit context
const createMockAudit = () => {
  const logs: Array<{ event: string; data: any; result?: any }> = [];
  return {
    log: (event: string, data: Record<string, any>, result?: any) => {
      logs.push({ event, data, result });
    },
    logs,
  };
};

// Use the main kelpie codebase which already has indexes
const codebasePath = join(process.cwd(), "../..");
const indexesPath = join(codebasePath, ".kelpie-index");
const agentfsPath = join(codebasePath, ".agentfs");

// Only run if indexes exist
const shouldRunTest = existsSync(indexesPath);

describe.skipIf(!shouldRunTest)("Phase 8.2: MCP Tool Integration", () => {
  beforeAll(() => {
    // Ensure AgentFS directory exists for state tests
    if (!existsSync(agentfsPath)) {
      mkdirSync(agentfsPath, { recursive: true });
    }
  });

  it("Should query symbols from existing indexes", async () => {
    const audit = createMockAudit();
    const context = {
      codebasePath,
      indexesPath,
      audit,
    };

    const tools = createIndexTools(context);
    const indexSymbols = tools.find((t) => t.name === "index_symbols");
    expect(indexSymbols).toBeDefined();

    const result = await (indexSymbols as any).handler({
      pattern: "Actor",
    });

    expect(result.success).toBe(true);
    expect(result.matches).toBeDefined();
    expect(Array.isArray(result.matches)).toBe(true);

    // Should have audit log entry
    expect((audit as any).logs.length).toBeGreaterThan(0);
    expect((audit as any).logs[0].event).toBe("index_symbols");
  });

  it("Should query tests from existing indexes", async () => {
    const audit = createMockAudit();
    const context = {
      codebasePath,
      indexesPath,
      audit,
    };

    const tools = createIndexTools(context);
    const indexTests = tools.find((t) => t.name === "index_tests");
    expect(indexTests).toBeDefined();

    const result = await (indexTests as any).handler({
      topic: "actor",
    });

    expect(result.success).toBe(true);
    expect(result.tests).toBeDefined();
    expect(Array.isArray(result.tests)).toBe(true);

    // Should have audit log entry
    expect((audit as any).logs.length).toBeGreaterThan(0);
    expect((audit as any).logs[0].event).toBe("index_tests");
  });

  it("Should query modules from existing indexes", async () => {
    const audit = createMockAudit();
    const context = {
      codebasePath,
      indexesPath,
      audit,
    };

    const tools = createIndexTools(context);
    const indexModules = tools.find((t) => t.name === "index_modules");
    expect(indexModules).toBeDefined();

    const result = await (indexModules as any).handler({});

    expect(result.success).toBe(true);
    expect(result.crates).toBeDefined();
    expect(Array.isArray(result.crates)).toBe(true);
    expect(result.crates.length).toBeGreaterThan(0);

    // Should have audit log entry
    expect((audit as any).logs.length).toBeGreaterThan(0);
    expect((audit as any).logs[0].event).toBe("index_modules");
  });

  it("Should query dependencies from existing indexes", async () => {
    const audit = createMockAudit();
    const context = {
      codebasePath,
      indexesPath,
      audit,
    };

    const tools = createIndexTools(context);
    const indexDeps = tools.find((t) => t.name === "index_deps");
    expect(indexDeps).toBeDefined();

    const result = await (indexDeps as any).handler({});

    expect(result.success).toBe(true);
    expect(result.nodes).toBeDefined();
    expect(result.edges).toBeDefined();
    expect(Array.isArray(result.nodes)).toBe(true);
    expect(Array.isArray(result.edges)).toBe(true);

    // Should have audit log entry
    expect((audit as any).logs.length).toBeGreaterThan(0);
    expect((audit as any).logs[0].event).toBe("index_deps");
  });

  it("Should check index status", async () => {
    const audit = createMockAudit();
    const context = {
      codebasePath,
      indexesPath,
      audit,
    };

    const tools = createIndexTools(context);
    const indexStatus = tools.find((t) => t.name === "index_status");
    expect(indexStatus).toBeDefined();

    const result = await (indexStatus as any).handler({});

    expect(result.success).toBe(true);
    expect(result.status).toBeDefined();
    expect(result.status.freshness).toBeDefined();
    expect(result.status.symbols).toBeDefined();
    expect(result.status.tests).toBeDefined();
    expect(result.status.modules).toBeDefined();
    expect(result.status.dependencies).toBeDefined();

    // Should have audit log entry
    expect((audit as any).logs.length).toBeGreaterThan(0);
    expect((audit as any).logs[0].event).toBe("index_status");
  });

  it("Should create and manage tasks via state tools", async () => {
    const audit = createMockAudit();
    const context = {
      agentfsPath,
      codebasePath,
      audit,
    };

    const tools = createStateTools(context);

    // Start a task
    const taskStart = tools.find((t) => t.name === "state_task_start");
    expect(taskStart).toBeDefined();

    const startResult = await (taskStart as any).handler({
      description: "Test tool integration",
    });

    expect(startResult.success).toBe(true);
    expect(startResult.task_id).toBeDefined();
    expect(startResult.started_at).toBeDefined();

    const taskId = startResult.task_id;

    // Get task state
    const stateGet = tools.find((t) => t.name === "state_get");
    expect(stateGet).toBeDefined();

    // Task start should have been logged
    expect((audit as any).logs.length).toBeGreaterThan(0);
    const taskStartLog = (audit as any).logs.find((l: any) => l.event === "task_start");
    expect(taskStartLog).toBeDefined();
  });

  it("Should validate cross-tool integration workflow", async () => {
    const audit = createMockAudit();
    const indexContext = {
      codebasePath,
      indexesPath,
      audit,
    };
    const stateContext = {
      agentfsPath,
      codebasePath,
      audit,
    };

    // 1. Start a task
    const stateTools = createStateTools(stateContext);
    const taskStart = stateTools.find((t) => t.name === "state_task_start");
    const taskResult = await (taskStart as any).handler({
      description: "Find and analyze Actor symbols",
    });
    expect(taskResult.success).toBe(true);

    // 2. Query symbols (simulating agent work)
    const indexTools = createIndexTools(indexContext);
    const indexSymbols = indexTools.find((t) => t.name === "index_symbols");
    const symbolResult = await (indexSymbols as any).handler({
      pattern: "Actor",
    });
    expect(symbolResult.success).toBe(true);

    // 3. Check index status
    const indexStatus = indexTools.find((t) => t.name === "index_status");
    const statusResult = await (indexStatus as any).handler({});
    expect(statusResult.success).toBe(true);

    // 4. Verify audit trail has all operations
    const auditLogs = (audit as any).logs;
    expect(auditLogs.length).toBe(3);

    const taskStartLog = auditLogs.find((l: any) => l.event === "task_start");
    expect(taskStartLog).toBeDefined();

    const symbolsLog = auditLogs.find((l: any) => l.event === "index_symbols");
    expect(symbolsLog).toBeDefined();

    const statusLog = auditLogs.find((l: any) => l.event === "index_status");
    expect(statusLog).toBeDefined();
  });
});
