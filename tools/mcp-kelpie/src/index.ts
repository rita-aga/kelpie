#!/usr/bin/env node
/**
 * MCP Server for Kelpie Repo OS
 *
 * Provides tools for:
 * - Index queries (symbols, tests, dependencies, modules)
 * - State management (AgentFS)
 * - Verification (running tests, checking claims)
 * - Hard controls (freshness gates, evidence requirements)
 *
 * TigerStyle: Hard controls enforce verification, not just guidance.
 */

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  Tool,
} from "@modelcontextprotocol/sdk/types.js";
import { existsSync } from "fs";
import { join } from "path";

// Import tool handlers
import { createStateTools, StateContext } from "./state.js";
import { createIndexTools, IndexContext } from "./indexes.js";
import { createVerificationTools, VerificationContext } from "./verify.js";
import { createIntegrityTools, IntegrityContext } from "./integrity.js";
import { createSlopTools, SlopContext } from "./slop.js";
import { createConstraintTools, ConstraintsContext } from "./constraints.js";
import { createRlmTools, RlmContext } from "./rlm.js";
import { createDstTools, DstContext } from "./dst.js";
import { createCodebaseTools, CodebaseContext } from "./codebase.js";
import { createAuditLogger } from "./audit.js";

/**
 * Server configuration
 * TigerStyle: Explicit paths with validation
 */
interface ServerConfig {
  codebasePath: string;
  indexesPath: string;
  agentfsPath: string;
}

/**
 * Load configuration from environment or defaults
 */
function loadConfig(): ServerConfig {
  // TigerStyle: Explicit defaults, validate existence
  const codebasePath = process.env.KELPIE_CODEBASE_PATH || process.cwd();
  const indexesPath = process.env.KELPIE_INDEXES_PATH || join(codebasePath, ".kelpie-index");
  const agentfsPath = process.env.KELPIE_AGENTFS_PATH || join(codebasePath, ".agentfs");

  // TigerStyle: Validate paths exist
  if (!existsSync(codebasePath)) {
    throw new Error(`Codebase path does not exist: ${codebasePath}`);
  }

  if (!existsSync(indexesPath)) {
    throw new Error(`Indexes path does not exist: ${indexesPath}`);
  }

  if (!existsSync(agentfsPath)) {
    throw new Error(`AgentFS path does not exist: ${agentfsPath}`);
  }

  return { codebasePath, indexesPath, agentfsPath };
}

/**
 * Main server initialization
 */
async function main() {
  const config = loadConfig();

  console.error(`[MCP Kelpie] Starting server`);
  console.error(`[MCP Kelpie] Codebase: ${config.codebasePath}`);
  console.error(`[MCP Kelpie] Indexes: ${config.indexesPath}`);
  console.error(`[MCP Kelpie] AgentFS: ${config.agentfsPath}`);

  // Initialize contexts
  const auditContext = createAuditLogger(config.agentfsPath);
  const stateContext: StateContext = {
    agentfsPath: config.agentfsPath,
    audit: auditContext,
  };
  const indexContext: IndexContext = {
    indexesPath: config.indexesPath,
    codebasePath: config.codebasePath,
    audit: auditContext,
  };
  const verifyContext: VerificationContext = {
    codebasePath: config.codebasePath,
    indexesPath: config.indexesPath,
    audit: auditContext,
  };
  const integrityContext: IntegrityContext = {
    codebasePath: config.codebasePath,
    agentfsPath: config.agentfsPath,
    audit: auditContext,
  };
  const slopContext: SlopContext = {
    codebasePath: config.codebasePath,
    indexesPath: config.indexesPath,
    audit: auditContext,
  };
  const constraintsContext: ConstraintsContext = {
    codebasePath: config.codebasePath,
    audit: auditContext,
  };
  const rlmContext: RlmContext = {
    codebasePath: config.codebasePath,
    indexesPath: config.indexesPath,
    audit: auditContext,
  };
  const dstContext: DstContext = {
    codebasePath: config.codebasePath,
    indexesPath: config.indexesPath,
    audit: auditContext,
  };
  const codebaseContext: CodebaseContext = {
    codebasePath: config.codebasePath,
    indexesPath: config.indexesPath,
    audit: auditContext,
  };

  // Create MCP server
  const server = new Server(
    {
      name: "kelpie-mcp-server",
      version: "0.1.0",
    },
    {
      capabilities: {
        tools: {},
      },
    }
  );

  // Collect all tools
  const stateTools = createStateTools(stateContext);
  const indexTools = createIndexTools(indexContext);
  const verificationTools = createVerificationTools(verifyContext);
  const integrityTools = createIntegrityTools(integrityContext);
  const slopTools = createSlopTools(slopContext);
  const constraintTools = createConstraintTools(constraintsContext);
  const rlmTools = createRlmTools(rlmContext);
  const dstTools = createDstTools(dstContext);
  const codebaseTools = createCodebaseTools(codebaseContext);

  const allTools: Tool[] = [
    ...stateTools,
    ...indexTools,
    ...verificationTools,
    ...integrityTools,
    ...slopTools,
    ...constraintTools,
    ...rlmTools,
    ...dstTools,
    ...codebaseTools,
  ];

  console.error(`[MCP Kelpie] Registered ${allTools.length} tools`);

  // List tools handler
  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return { tools: allTools };
  });

  // Call tool handler
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;

    // Log tool call
    auditContext.log("tool_call", { tool: name, args });

    try {
      // Route to appropriate handler
      const stateTool = stateTools.find((t) => t.name === name);
      if (stateTool) {
        const handler = (stateTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const indexTool = indexTools.find((t) => t.name === name);
      if (indexTool) {
        const handler = (indexTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const verifyTool = verificationTools.find((t) => t.name === name);
      if (verifyTool) {
        const handler = (verifyTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const integrityTool = integrityTools.find((t) => t.name === name);
      if (integrityTool) {
        const handler = (integrityTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const slopTool = slopTools.find((t) => t.name === name);
      if (slopTool) {
        const handler = (slopTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const constraintTool = constraintTools.find((t) => t.name === name);
      if (constraintTool) {
        const handler = (constraintTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const rlmTool = rlmTools.find((t) => t.name === name);
      if (rlmTool) {
        const handler = (rlmTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const dstTool = dstTools.find((t) => t.name === name);
      if (dstTool) {
        const handler = (dstTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      const codebaseTool = codebaseTools.find((t) => t.name === name);
      if (codebaseTool) {
        const handler = (codebaseTool as any).handler;
        if (!handler) {
          throw new Error(`Tool ${name} has no handler`);
        }
        const result = await handler(args || {});
        return {
          content: [{ type: "text" as const, text: JSON.stringify(result, null, 2) }],
        };
      }

      throw new Error(`Unknown tool: ${name}`);
    } catch (error) {
      const errorMessage = error instanceof Error ? error.message : String(error);
      auditContext.log("tool_error", { tool: name, error: errorMessage });
      return {
        content: [{ type: "text" as const, text: JSON.stringify({ error: errorMessage }) }],
        isError: true,
      };
    }
  });

  // Start server with stdio transport
  const transport = new StdioServerTransport();
  await server.connect(transport);

  console.error("[MCP Kelpie] Server running on stdio");
}

// Run server
main().catch((error) => {
  console.error("[MCP Kelpie] Fatal error:", error);
  process.exit(1);
});
