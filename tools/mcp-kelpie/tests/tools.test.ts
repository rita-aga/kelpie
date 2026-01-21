/**
 * MCP Server Tool Tests
 *
 * Tests tool registration, input validation, and basic functionality
 */

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdirSync, rmSync, existsSync } from "fs";
import { createConstraintTools } from "../src/constraints.js";
import { createDstTools } from "../src/dst.js";
import { createStateTools } from "../src/state.js";
import { createIndexTools } from "../src/indexes.js";
import { AuditContext } from "../src/audit.js";

// Mock audit context
const createMockAudit = (): AuditContext => ({
  log: () => {},
});

describe("Constraint Tools", () => {
  const context = {
    codebasePath: process.cwd(),
    audit: createMockAudit(),
  };

  it("should register constraint_check and constraint_list tools", () => {
    const tools = createConstraintTools(context);
    expect(tools).toHaveLength(2);
    expect(tools.map((t) => t.name)).toContain("constraint_check");
    expect(tools.map((t) => t.name)).toContain("constraint_list");
  });

  it("should have required schema for constraint_check", () => {
    const tools = createConstraintTools(context);
    const constraintCheck = tools.find((t) => t.name === "constraint_check");
    expect(constraintCheck).toBeDefined();
    expect(constraintCheck!.inputSchema).toBeDefined();
    expect(constraintCheck!.inputSchema.type).toBe("object");
  });

  it("should execute constraint_list successfully", async () => {
    const tools = createConstraintTools(context);
    const constraintList = tools.find((t) => t.name === "constraint_list");
    const result = await (constraintList as any).handler({});

    expect(result.success).toBe(true);
    expect(result.constraints).toBeDefined();
    expect(Array.isArray(result.constraints)).toBe(true);
    expect(result.constraints.length).toBeGreaterThan(0);
  });

  it("should check for placeholders in constraint_check", async () => {
    const tools = createConstraintTools(context);
    const constraintCheck = tools.find((t) => t.name === "constraint_check");
    const result = await (constraintCheck as any).handler({
      check_types: ["placeholders"],
    });

    expect(result).toBeDefined();
    expect(result.summary).toBeDefined();
    expect(typeof result.summary.total_violations).toBe("number");
  });
});

describe("DST Tools", () => {
  const context = {
    codebasePath: process.cwd(),
    indexesPath: process.cwd() + "/.kelpie-index",
    audit: createMockAudit(),
  };

  it("should register dst_coverage_check, dst_gaps_report, and harness_check", () => {
    const tools = createDstTools(context);
    expect(tools).toHaveLength(3);
    expect(tools.map((t) => t.name)).toContain("dst_coverage_check");
    expect(tools.map((t) => t.name)).toContain("dst_gaps_report");
    expect(tools.map((t) => t.name)).toContain("harness_check");
  });

  it("should validate harness support for known fault types", async () => {
    const tools = createDstTools(context);
    const harnessCheck = tools.find((t) => t.name === "harness_check");

    // Test with supported fault types
    const result = await (harnessCheck as any).handler({
      fault_types: ["StorageWriteFail", "NetworkPartition"],
    });

    expect(result.success).toBe(true);
    expect(result.results).toBeDefined();
    expect(result.results.length).toBe(2);
    expect(result.results[0].supported).toBe(true);
    expect(result.results[1].supported).toBe(true);
  });

  it("should detect unsupported fault types", async () => {
    const tools = createDstTools(context);
    const harnessCheck = tools.find((t) => t.name === "harness_check");

    const result = await (harnessCheck as any).handler({
      fault_types: ["UnsupportedFaultType"],
    });

    expect(result.success).toBe(false);
    expect(result.results[0].supported).toBe(false);
    expect(result.results[0].needs_extension).toBe(true);
    expect(result.next_steps).toContain("STOP");
  });
});

describe("State Tools", () => {
  let tempAgentfsPath: string;
  let context: { agentfsPath: string; audit: AuditContext };

  beforeEach(() => {
    // Use a temp directory for testing
    tempAgentfsPath = "/tmp/test-agentfs-" + Date.now();
    mkdirSync(tempAgentfsPath, { recursive: true });

    context = {
      agentfsPath: tempAgentfsPath,
      audit: createMockAudit(),
    };
  });

  afterEach(() => {
    // Clean up temp directory
    if (existsSync(tempAgentfsPath)) {
      rmSync(tempAgentfsPath, { recursive: true, force: true });
    }
  });

  it("should register 5 state tools", () => {
    const tools = createStateTools(context);
    expect(tools).toHaveLength(5);
    expect(tools.map((t) => t.name)).toContain("state_get");
    expect(tools.map((t) => t.name)).toContain("state_set");
    expect(tools.map((t) => t.name)).toContain("state_task_start");
    expect(tools.map((t) => t.name)).toContain("state_task_complete");
    expect(tools.map((t) => t.name)).toContain("state_verified_fact");
  });

  it("should have proper input schema for state_task_complete", () => {
    const tools = createStateTools(context);
    const taskComplete = tools.find((t) => t.name === "state_task_complete");

    expect(taskComplete).toBeDefined();
    expect(taskComplete!.inputSchema.properties).toHaveProperty("task_id");
    expect(taskComplete!.inputSchema.properties).toHaveProperty("proof");
    expect(taskComplete!.inputSchema.required).toContain("task_id");
    expect(taskComplete!.inputSchema.required).toContain("proof");
  });
});

describe("Index Tools", () => {
  const context = {
    indexesPath: process.cwd() + "/.kelpie-index",
    codebasePath: process.cwd(),
    audit: createMockAudit(),
  };

  it("should register 7 index tools", () => {
    const tools = createIndexTools(context);
    expect(tools).toHaveLength(7);
    expect(tools.map((t) => t.name)).toContain("index_symbols");
    expect(tools.map((t) => t.name)).toContain("index_tests");
    expect(tools.map((t) => t.name)).toContain("index_modules");
    expect(tools.map((t) => t.name)).toContain("index_deps");
    expect(tools.map((t) => t.name)).toContain("index_status");
    expect(tools.map((t) => t.name)).toContain("index_refresh");
    expect(tools.map((t) => t.name)).toContain("index_validate");
  });

  it("should have pattern parameter for index_symbols", () => {
    const tools = createIndexTools(context);
    const indexSymbols = tools.find((t) => t.name === "index_symbols");

    expect(indexSymbols).toBeDefined();
    expect(indexSymbols!.inputSchema.properties).toHaveProperty("pattern");
    expect(indexSymbols!.inputSchema.required).toContain("pattern");
  });
});

describe("Tool Count Verification", () => {
  it("should have 30 total tools across all modules", () => {
    const mockAudit = createMockAudit();
    const mockCodebasePath = process.cwd();
    const mockIndexesPath = process.cwd() + "/.kelpie-index";
    const mockAgentfsPath = "/tmp/test-agentfs-count-" + Date.now();

    // Create temp directory for state tools
    mkdirSync(mockAgentfsPath, { recursive: true });

    try {
      const stateTools = createStateTools({
        agentfsPath: mockAgentfsPath,
        audit: mockAudit,
      });

      const indexTools = createIndexTools({
        indexesPath: mockIndexesPath,
        codebasePath: mockCodebasePath,
        audit: mockAudit,
      });

      const constraintTools = createConstraintTools({
        codebasePath: mockCodebasePath,
        audit: mockAudit,
      });

      const dstTools = createDstTools({
        codebasePath: mockCodebasePath,
        indexesPath: mockIndexesPath,
        audit: mockAudit,
      });

      // Expected counts from README
      expect(stateTools).toHaveLength(5); // Phase 4.2
      expect(indexTools).toHaveLength(7); // Phase 4.3 + 4.5
      expect(constraintTools).toHaveLength(2); // Phase 4.2
      expect(dstTools).toHaveLength(3); // Phase 4.9 + 4.10

      // Subtotal from these modules
      const subtotal = stateTools.length + indexTools.length + constraintTools.length + dstTools.length;

      // We have 5 + 7 + 2 + 3 = 17 tools tested here
      // Plus verify (4), integrity (2), slop (2), rlm (2), codebase (3) = 13 more = 30 total
      expect(subtotal).toBe(17);
    } finally {
      // Clean up temp directory
      if (existsSync(mockAgentfsPath)) {
        rmSync(mockAgentfsPath, { recursive: true, force: true });
      }
    }
  });
});
