"""
Spec Adapter Framework for Codebase Intelligence

Phase 10.1: Normalizes ANY specification into comparable requirements.

The IS vs SHOULD framework:
- SHOULD: What the spec says should be true (requirements)
- IS: What actually exists in the code (reality)
- ISSUE: When IS doesn't match SHOULD

Adapters:
- OpenAPIAdapter: For API compatibility specs (Letta, etc.)
- PatternRuleAdapter: For structural requirements (DST coverage, etc.)
- TLAPlusAdapter: For formal specifications
- TypeContractAdapter: For type-level requirements from code

TigerStyle: Explicit contracts, no silent failures.
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional
import json
import re
import yaml


class RequirementType(Enum):
    """Types of requirements that can be extracted from specs."""
    API_ENDPOINT = "api_endpoint"
    API_SCHEMA = "api_schema"
    STRUCTURAL_PATTERN = "structural_pattern"
    DST_COVERAGE = "dst_coverage"
    TYPE_CONTRACT = "type_contract"
    INVARIANT = "invariant"
    BEHAVIOR = "behavior"


@dataclass
class Requirement:
    """
    Normalized requirement from any spec source.
    
    This is the common currency - all adapters produce these,
    and the examination workflow consumes them.
    """
    id: str
    source: str  # e.g., "letta_openapi", "dst_rules", "actor.tla"
    req_type: RequirementType
    description: str  # Human-readable expectation
    verification_hint: str  # Guidance for examining agent
    context: Dict[str, Any] = field(default_factory=dict)  # Source-specific details
    
    # Optional: scope hints
    applies_to_patterns: List[str] = field(default_factory=list)  # File/module patterns
    priority: int = 1  # 1=high, 2=medium, 3=low
    
    def applies_to(self, module_path: str) -> bool:
        """Check if this requirement applies to a given module/file."""
        if not self.applies_to_patterns:
            return True  # Applies everywhere if no patterns specified
        
        for pattern in self.applies_to_patterns:
            if re.search(pattern, module_path):
                return True
        return False


class SpecAdapter(ABC):
    """
    Base class for normalizing specs to requirements.
    
    Each adapter knows how to read a specific spec format and
    extract requirements in the normalized Requirement format.
    """
    
    @property
    @abstractmethod
    def source_name(self) -> str:
        """Name of this spec source (e.g., 'letta_openapi')."""
        pass
    
    @abstractmethod
    def load(self, source_path: str) -> List[Requirement]:
        """Load and parse specification into requirements."""
        pass
    
    @abstractmethod
    def can_load(self, source_path: str) -> bool:
        """Check if this adapter can handle the given source."""
        pass


class OpenAPIAdapter(SpecAdapter):
    """
    Adapter for OpenAPI specifications.
    
    Extracts:
    - Endpoints (paths, methods)
    - Request/response schemas
    - Required parameters
    - Behavioral constraints from descriptions
    
    Source: OpenAPI YAML/JSON files
    """
    
    @property
    def source_name(self) -> str:
        return "openapi"
    
    def can_load(self, source_path: str) -> bool:
        path = Path(source_path)
        if not path.exists():
            return False
        
        # Check file extension
        if path.suffix.lower() not in ['.yaml', '.yml', '.json']:
            return False
        
        # Try to detect OpenAPI format
        try:
            content = self._load_file(source_path)
            return 'openapi' in content or 'swagger' in content
        except Exception:
            return False
    
    def _load_file(self, source_path: str) -> Dict:
        """Load YAML or JSON file."""
        path = Path(source_path)
        with open(path, 'r') as f:
            if path.suffix.lower() == '.json':
                return json.load(f)
            else:
                return yaml.safe_load(f)
    
    def load(self, source_path: str) -> List[Requirement]:
        """Extract requirements from OpenAPI spec."""
        spec = self._load_file(source_path)
        requirements = []
        
        # Extract from paths
        paths = spec.get('paths', {})
        for path, methods in paths.items():
            for method, details in methods.items():
                if method.lower() in ['get', 'post', 'put', 'delete', 'patch']:
                    req = self._extract_endpoint_requirement(
                        path, method, details, source_path
                    )
                    requirements.append(req)
        
        # Extract from schemas (components)
        schemas = spec.get('components', {}).get('schemas', {})
        for schema_name, schema_def in schemas.items():
            req = self._extract_schema_requirement(
                schema_name, schema_def, source_path
            )
            requirements.append(req)
        
        return requirements
    
    def _extract_endpoint_requirement(
        self, path: str, method: str, details: Dict, source: str
    ) -> Requirement:
        """Extract requirement for an API endpoint."""
        operation_id = details.get('operationId', f'{method}_{path}')
        summary = details.get('summary', '')
        description = details.get('description', '')
        
        # Determine which modules this applies to
        # Convention: /v1/agents/* -> agent-related modules
        patterns = []
        if '/agents' in path:
            patterns.append(r'(agent|letta)')
        if '/messages' in path:
            patterns.append(r'message')
        if '/memory' in path or '/archival' in path:
            patterns.append(r'memory')
        
        return Requirement(
            id=f"api_{operation_id}",
            source=f"{self.source_name}:{source}",
            req_type=RequirementType.API_ENDPOINT,
            description=f"API endpoint {method.upper()} {path}: {summary}",
            verification_hint=f"Check that {method.upper()} {path} is implemented with correct request/response handling. {description}",
            context={
                "path": path,
                "method": method.upper(),
                "operation_id": operation_id,
                "parameters": details.get('parameters', []),
                "request_body": details.get('requestBody'),
                "responses": details.get('responses', {}),
            },
            applies_to_patterns=patterns,
        )
    
    def _extract_schema_requirement(
        self, name: str, schema: Dict, source: str
    ) -> Requirement:
        """Extract requirement for a schema."""
        required_fields = schema.get('required', [])
        properties = schema.get('properties', {})
        
        return Requirement(
            id=f"schema_{name}",
            source=f"{self.source_name}:{source}",
            req_type=RequirementType.API_SCHEMA,
            description=f"Schema {name} with required fields: {required_fields}",
            verification_hint=f"Verify that {name} type exists with all required fields: {required_fields}",
            context={
                "schema_name": name,
                "required_fields": required_fields,
                "properties": properties,
                "type": schema.get('type'),
            },
            applies_to_patterns=[r'models?|types?|schema'],
        )


class PatternRuleAdapter(SpecAdapter):
    """
    Adapter for pattern-based structural requirements.
    
    Extracts:
    - File/function patterns that must exist
    - Required test coverage
    - Structural rules (e.g., "every pub async fn needs DST")
    
    Source: YAML rule files
    """
    
    @property
    def source_name(self) -> str:
        return "pattern_rules"
    
    def can_load(self, source_path: str) -> bool:
        path = Path(source_path)
        if not path.exists():
            return False
        
        if path.suffix.lower() not in ['.yaml', '.yml']:
            return False
        
        try:
            with open(path, 'r') as f:
                content = yaml.safe_load(f)
            return 'rules' in content or 'patterns' in content
        except Exception:
            return False
    
    def load(self, source_path: str) -> List[Requirement]:
        """Extract requirements from pattern rules."""
        with open(source_path, 'r') as f:
            spec = yaml.safe_load(f)
        
        requirements = []
        
        for rule in spec.get('rules', []):
            req = self._extract_rule_requirement(rule, source_path)
            requirements.append(req)
        
        return requirements
    
    def _extract_rule_requirement(self, rule: Dict, source: str) -> Requirement:
        """Extract requirement from a single rule."""
        rule_id = rule.get('id', 'unknown')
        description = rule.get('description', '')
        file_pattern = rule.get('file_pattern', '')
        function_pattern = rule.get('function_pattern', '')
        required = rule.get('required', {})
        
        # Determine requirement type
        req_type = RequirementType.STRUCTURAL_PATTERN
        if 'dst' in rule_id.lower() or 'test' in required:
            req_type = RequirementType.DST_COVERAGE
        
        return Requirement(
            id=f"rule_{rule_id}",
            source=f"{self.source_name}:{source}",
            req_type=req_type,
            description=description,
            verification_hint=f"Check files matching {file_pattern} for functions matching {function_pattern}. Required: {required}",
            context={
                "file_pattern": file_pattern,
                "function_pattern": function_pattern,
                "required": required,
            },
            applies_to_patterns=[file_pattern] if file_pattern else [],
        )


class DSTCoverageAdapter(SpecAdapter):
    """
    Specialized adapter for DST coverage requirements.
    
    Extracts requirements for:
    - What code paths need DST tests
    - What fault types must be injected
    - What determinism properties must hold
    
    Source: DST coverage YAML files
    """
    
    @property
    def source_name(self) -> str:
        return "dst_rules"
    
    def can_load(self, source_path: str) -> bool:
        path = Path(source_path)
        if not path.exists():
            return False
        
        name = path.name.lower()
        return 'dst' in name and path.suffix.lower() in ['.yaml', '.yml']
    
    def load(self, source_path: str) -> List[Requirement]:
        """Extract DST coverage requirements."""
        with open(source_path, 'r') as f:
            spec = yaml.safe_load(f)
        
        requirements = []
        
        for rule in spec.get('rules', []):
            req = Requirement(
                id=f"dst_{rule.get('id', 'unknown')}",
                source=f"{self.source_name}:{source_path}",
                req_type=RequirementType.DST_COVERAGE,
                description=rule.get('description', ''),
                verification_hint=self._build_dst_hint(rule),
                context={
                    "file_pattern": rule.get('file_pattern', ''),
                    "function_pattern": rule.get('function_pattern', ''),
                    "test_file_suffix": rule.get('required', {}).get('test_file_suffix', '_dst.rs'),
                    "fault_injection": rule.get('required', {}).get('fault_injection', []),
                },
                applies_to_patterns=[rule.get('file_pattern', '')] if rule.get('file_pattern') else [],
            )
            requirements.append(req)
        
        return requirements
    
    def _build_dst_hint(self, rule: Dict) -> str:
        """Build verification hint for DST requirement."""
        required = rule.get('required', {})
        hints = []
        
        if required.get('test_file_suffix'):
            hints.append(f"Test file suffix: {required['test_file_suffix']}")
        
        if required.get('fault_injection'):
            faults = ', '.join(required['fault_injection'])
            hints.append(f"Required fault injection: {faults}")
        
        if required.get('determinism'):
            hints.append("Must be deterministic (run twice with same seed, same result)")
        
        return "; ".join(hints)


# Registry of available adapters
ADAPTERS: List[SpecAdapter] = [
    OpenAPIAdapter(),
    PatternRuleAdapter(),
    DSTCoverageAdapter(),
]


def load_spec(source_path: str) -> List[Requirement]:
    """
    Load a spec file using the appropriate adapter.
    
    Auto-detects the spec type and uses the right adapter.
    """
    for adapter in ADAPTERS:
        if adapter.can_load(source_path):
            return adapter.load(source_path)
    
    raise ValueError(f"No adapter found for spec: {source_path}")


def load_specs(source_paths: List[str]) -> List[Requirement]:
    """Load multiple spec files and combine requirements."""
    all_requirements = []
    for path in source_paths:
        try:
            reqs = load_spec(path)
            all_requirements.extend(reqs)
        except Exception as e:
            print(f"Warning: Failed to load spec {path}: {e}")
    return all_requirements


def filter_requirements(
    requirements: List[Requirement],
    module_path: Optional[str] = None,
    req_type: Optional[RequirementType] = None,
) -> List[Requirement]:
    """Filter requirements by module and/or type."""
    result = requirements
    
    if module_path:
        result = [r for r in result if r.applies_to(module_path)]
    
    if req_type:
        result = [r for r in result if r.req_type == req_type]
    
    return result
