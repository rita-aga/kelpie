# @kelpie/client

TypeScript client for the Kelpie agent runtime.

## Installation

```bash
npm install @kelpie/client
```

## Usage

```typescript
import { KelpieClient } from '@kelpie/client';

const client = new KelpieClient('http://localhost:8283');

// Create an agent
const agent = await client.createAgent({
  name: 'my-agent',
  system: 'You are a helpful assistant.',
  memory_blocks: [
    { label: 'persona', value: 'I am a friendly AI assistant.' },
    { label: 'human', value: 'The user is a developer.' }
  ]
});

// Send a message
const response = await client.sendMessage(agent.id, 'Hello!');
console.log(response.messages[1].content);

// Update memory block
const blocks = await client.listBlocks(agent.id);
await client.updateBlock(agent.id, blocks[0].id, {
  value: 'Updated persona information.'
});

// List message history
const messages = await client.listMessages(agent.id);
```

## API Reference

### KelpieClient

#### Constructor

```typescript
new KelpieClient(baseUrl?: string, timeout?: number)
```

- `baseUrl`: Server URL (default: `http://localhost:8283`)
- `timeout`: Request timeout in milliseconds (default: `30000`)

#### Agent Methods

- `createAgent(request)` - Create a new agent
- `getAgent(agentId)` - Get agent by ID
- `listAgents(limit?, cursor?)` - List agents with pagination
- `updateAgent(agentId, update)` - Update agent properties
- `deleteAgent(agentId)` - Delete an agent

#### Block Methods

- `listBlocks(agentId)` - List memory blocks for an agent
- `getBlock(agentId, blockId)` - Get a specific block
- `updateBlock(agentId, blockId, update)` - Update a block

#### Message Methods

- `sendMessage(agentId, content, role?)` - Send a message and get response
- `listMessages(agentId, limit?, before?)` - List message history

#### Health Check

- `health()` - Check server health

## License

Apache-2.0
