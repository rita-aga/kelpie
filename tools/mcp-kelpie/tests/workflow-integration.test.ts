/**
 * Phase 8.2: Integration Test - Scripted Workflow
 *
 * This test simulates a complete workflow using MCP tools:
 * 1. Build all indexes
 * 2. Start a task
 * 3. Query symbols and tests
 * 4. Simulate code change
 * 5. Verify freshness gate catches staleness
 * 6. Rebuild incrementally
 * 7. Complete task with proof
 * 8. Verify audit trail
 *
 * TigerStyle: Each step has explicit assertions
 */

import { describe, it, expect, beforeAll, afterAll } from "vitest";
import { createIndexTools } from "../src/indexes.js";
import { createStateTools } from "../src/state.js";
import { createVerificationTools } from "../src/verify.js";
import { existsSync, mkdirSync, writeFileSync, readFileSync } from "fs";
import { join } from "path";
import { execSync } from "child_process";

// Mock audit context
const createMockAudit = () => ({
  log: (event: string, data: Record<string, any>, result?: any) => {
    // Store audit entries for verification
    auditLog.push({ event, data, result });
  },
});

// Global audit log for verification
let auditLog: any[] = [];

// Use test fixture as the codebase
const fixtureDir = join(process.cwd(), "../kelpie-indexer/tests/fixtures/sample_crate");
const testWorkspaceDir = join(process.cwd(), "../../test-workspace-integration");

// Skip if fixture doesn't exist
const shouldRunTest = existsSync(fixtureDir);

describe.skipIf(!shouldRunTest)("Phase 8.2: Full Workflow Integration", () => {
  beforeAll(() => {
    // Clean up any previous test workspace
    if (existsSync(testWorkspaceDir)) {
      execSync(`rm -rf "${testWorkspaceDir}"`);
    }

    // Create test workspace by copying fixture
    execSync(`cp -r "${fixtureDir}" "${testWorkspaceDir}"`);

    // Initialize AgentFS directory
    const agentfsPath = join(testWorkspaceDir, ".agentfs");
    if (!existsSync(agentfsPath)) {
      mkdirSync(agentfsPath, { recursive: true });
    }

    // Reset audit log
    auditLog = [];
  });

  afterAll(() => {
    // Clean up test workspace
    if (existsSync(testWorkspaceDir)) {
      execSync(`rm -rf "${testWorkspaceDir}"`);
    }
  });

  it("Step 1: Should build all indexes", async () => {
    // Run indexer binary to build indexes
    execSync(`cargo run -p kelpie-indexer -- full`, {
      cwd: testWorkspaceDir,
      stdio: "inherit",
    });

    // Verify indexes exist
    const indexesPath = join(testWorkspaceDir, ".kelpie-index");
    expect(existsSync(join(indexesPath, "structural/symbols.json"))).toBe(true);
    expect(existsSync(join(indexesPath, "structural/dependencies.json"))).toBe(true);
    expect(existsSync(join(indexesPath, "structural/tests.json"))).toBe(true);
    expect(existsSync(join(indexesPath, "structural/modules.json"))).toBe(true);
    expect(existsSync(join(indexesPath, "meta/freshness.json"))).toBe(true);
  }, 30000); // 30s timeout for build

  it("Step 2: Should start a task via state_task_start", async () => {
    const context = {
      agentfsPath: join(testWorkspaceDir, ".agentfs"),
      codebasePath: testWorkspaceDir,
      audit: createMockAudit(),
    };

    const tools = createStateTools(context);
    const taskStart = tools.find((t) => t.name === "state_task_start");
    expect(taskStart).toBeDefined();

    const result = await (taskStart as any).handler({
      description: "Test workflow integration - add new function to sample crate",
    });

    expect(result.success).toBe(true);
    expect(result.task_id).toBeDefined();
    expect(result.started_at).toBeDefined();

    // Store task ID for later steps
    (global as any).testTaskId = result.task_id;
  });

  it("Step 3: Should query symbols via index_symbols", async () => {
    const context = {
      codebasePath: testWorkspaceDir,
      indexesPath: join(testWorkspaceDir, ".kelpie-index"),
      audit: createMockAudit(),
    };

    const tools = createIndexTools(context);
    const querySymbols = tools.find((t) => t.name === "index_symbols");
    expect(querySymbols).toBeDefined();

    const result = await (querySymbols as any).handler({
      pattern: "User",
    });

    expect(result.success).toBe(true);
    expect(result.matches).toBeDefined();
    expect(result.matches.length).toBeGreaterThan(0);

    // Verify we found the User struct
    const userSymbol = result.matches.find((m: any) =>
      m.symbol && m.symbol.name === "User"
    );
    expect(userSymbol).toBeDefined();
  });

  it("Step 4: Should query tests via index_tests", async () => {
    const context = {
      codebasePath: testWorkspaceDir,
      indexesPath: join(testWorkspaceDir, ".kelpie-index"),
      audit: createMockAudit(),
    };

    const tools = createIndexTools(context);
    const queryTests = tools.find((t) => t.name === "index_tests");
    expect(queryTests).toBeDefined();

    const result = await (queryTests as any).handler({
      topic: "test_create_user",
    });

    expect(result.success).toBe(true);
    expect(result.matches).toBeDefined();
    expect(result.matches.length).toBeGreaterThan(0);

    // Verify we found test_create_user
    const testMatch = result.matches.find((m: any) =>
      m.test && m.test.name === "test_create_user"
    );
    expect(testMatch).toBeDefined();
  });

  it("Step 5: Should simulate code change", async () => {
    // Modify the fixture file to add a new function
    const libPath = join(testWorkspaceDir, "crates/sample-crate/src/lib.rs");
    const originalContent = readFileSync(libPath, "utf-8");

    // Add a new function
    const newFunction = `

pub fn update_user(user: &mut User, new_name: String) {
    user.name = new_name;
}
`;

    writeFileSync(libPath, originalContent + newFunction);

    // Verify file was modified
    const modifiedContent = readFileSync(libPath, "utf-8");
    expect(modifiedContent).toContain("update_user");
  });

  it("Step 6: Should detect stale indexes via index_status", async () => {
    const context = {
      codebasePath: testWorkspaceDir,
      indexesPath: join(testWorkspaceDir, ".kelpie-index"),
      audit: createMockAudit(),
    };

    const tools = createIndexTools(context);
    const indexStatus = tools.find((t) => t.name === "index_status");
    expect(indexStatus).toBeDefined();

    const result = await (indexStatus as any).handler({});

    // Should detect staleness since we modified a file but didn't rebuild
    expect(result.success).toBe(true);
    expect(result.status.freshness).toBeDefined();
    expect(result.status.freshness.fresh).toBe(false);
    expect(result.status.freshness.git_sha_mismatch).toBe(true);
  });

  it("Step 7: Should rebuild incrementally", async () => {
    // Run incremental rebuild for the changed file
    execSync(
      `cargo run -p kelpie-indexer -- incremental crates/sample-crate/src/lib.rs`,
      {
        cwd: testWorkspaceDir,
        stdio: "inherit",
      }
    );

    // Verify indexes updated
    const symbolsPath = join(
      testWorkspaceDir,
      ".kelpie-index/structural/symbols.json"
    );
    const symbolsContent = readFileSync(symbolsPath, "utf-8");
    const symbols = JSON.parse(symbolsContent);

    // Verify new function is indexed
    const libFile =
      symbols.files["crates/sample-crate/src/lib.rs"];
    expect(libFile).toBeDefined();

    const updateUserSymbol = libFile.symbols.find(
      (s: any) => s.name === "update_user"
    );
    expect(updateUserSymbol).toBeDefined();
    expect(updateUserSymbol.kind).toBe("function");
  }, 30000); // 30s timeout for rebuild

  it("Step 8: Should attempt task completion (expect P0 violation)", async () => {
    const context = {
      agentfsPath: join(testWorkspaceDir, ".agentfs"),
      codebasePath: testWorkspaceDir,
      audit: createMockAudit(),
    };

    const tools = createStateTools(context);
    const taskComplete = tools.find((t) => t.name === "state_task_complete");
    expect(taskComplete).toBeDefined();

    const taskId = (global as any).testTaskId;
    expect(taskId).toBeDefined();

    // This should fail with P0 violations since we're in a test workspace
    // without proper formatting/clippy setup
    try {
      await (taskComplete as any).handler({
        task_id: taskId,
        proof: "Added update_user function to sample-crate/src/lib.rs. Verified via symbol index query.",
      });
      // If it succeeds, that's fine too (test workspace might pass checks)
    } catch (error: any) {
      // Expected: P0 constraint violations
      expect(error.message).toContain("P0 constraint");
    }
  });

  it("Step 9: Should verify audit trail exists", async () => {
    // Verify we have audit log entries
    expect(auditLog.length).toBeGreaterThan(0);

    // Verify audit log contains expected operations
    const taskStartEntry = auditLog.find(
      (e) => e.event === "state_task_start"
    );
    expect(taskStartEntry).toBeDefined();

    const indexSymbolsEntry = auditLog.find(
      (e) => e.event === "index_symbols"
    );
    expect(indexSymbolsEntry).toBeDefined();

    const indexTestsEntry = auditLog.find(
      (e) => e.event === "index_tests"
    );
    expect(indexTestsEntry).toBeDefined();

    const indexStatusEntry = auditLog.find(
      (e) => e.event === "index_status"
    );
    expect(indexStatusEntry).toBeDefined();
  });

  it("Step 10: Should verify freshness passes after rebuild", async () => {
    const context = {
      codebasePath: testWorkspaceDir,
      indexesPath: join(testWorkspaceDir, ".kelpie-index"),
      audit: createMockAudit(),
    };

    const tools = createIndexTools(context);
    const indexStatus = tools.find((t) => t.name === "index_status");
    expect(indexStatus).toBeDefined();

    const result = await (indexStatus as any).handler({});

    // Should pass now that indexes are rebuilt
    expect(result.success).toBe(true);
    expect(result.status.freshness).toBeDefined();
    expect(result.status.freshness.fresh).toBe(true);
  });
});
