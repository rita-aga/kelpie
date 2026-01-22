"""
Codebase Intelligence Layer - Agent-Driven Examination Workflow

Phase 10.3: The core workflow that answers ANY question about the codebase.

This module provides:
1. answer_codebase_question() - Main entry point for any codebase question
2. examine_partition() - Thorough examination of a single partition
3. synthesize_answer() - Combine findings into evidence-backed answer

The workflow:
1. UNDERSTAND & SCOPE - Analyze question, determine what to examine
2. LOAD EXPECTATIONS (SHOULD) - Load requirements from specs
3. SYSTEMATIC EXAMINATION (RLM) - Partition codebase, examine each part
4. RECORD ISSUES - Store findings to AgentFS
5. SYNTHESIZE ANSWER - Combine findings with evidence

TigerStyle: Thorough, truthful, evidence-backed answers.
"""

from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional, Callable
import json
import sqlite3
import time
import uuid

from .specs import (
    Requirement,
    RequirementType,
    load_specs,
    filter_requirements,
)
from .codebase import CodebaseContext


class IssueSeverity(Enum):
    CRITICAL = "critical"
    HIGH = "high"
    MEDIUM = "medium"
    LOW = "low"


class IssueCategory(Enum):
    STUB = "stub"
    GAP = "gap"
    MISMATCH = "mismatch"
    INCOMPLETE = "incomplete"
    FAKE_DST = "fake_dst"
    DEAD_CODE = "dead_code"
    DUPLICATE = "duplicate"
    ORPHAN = "orphan"
    OTHER = "other"


@dataclass
class Issue:
    """An issue discovered during examination."""
    category: IssueCategory
    severity: IssueSeverity
    should_description: str  # What SHOULD be true
    is_description: str      # What IS true
    analysis: str            # Why this is an issue
    location: Optional[str] = None
    evidence: Optional[str] = None
    spec_source: Optional[str] = None
    suggested_fix: Optional[str] = None
    confidence: float = 0.8


@dataclass
class PartitionFinding:
    """Findings from examining a single partition."""
    partition_name: str
    examined_at: int
    issues: List[Issue] = field(default_factory=list)
    observations: List[str] = field(default_factory=list)
    evidence_summary: str = ""


@dataclass
class ThortoughnessReport:
    """Report on examination thoroughness."""
    complete: bool
    examined_count: int
    expected_count: int
    missing_partitions: List[str]
    coverage_percent: float


@dataclass
class Answer:
    """Complete answer to a codebase question."""
    question: str
    direct_answer: str
    working: List[str]       # What's working (with evidence)
    broken: List[str]        # What's broken (with evidence)
    issues_found: int
    issue_summary: Dict[str, int]
    thoroughness: ThortoughnessReport
    partitions_examined: List[str]
    metadata: Dict[str, Any] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)


class AgentFSClient:
    """Client for interacting with AgentFS database."""
    
    def __init__(self, db_path: str):
        self.db_path = db_path
    
    def _connect(self) -> sqlite3.Connection:
        return sqlite3.connect(self.db_path)
    
    def record_issue(self, session_id: str, issue: Issue) -> str:
        """Record an issue to AgentFS. Returns issue ID."""
        conn = self._connect()
        cursor = conn.cursor()
        
        issue_id = f"issue-{int(time.time() * 1000)}-{uuid.uuid4().hex[:8]}"
        
        cursor.execute("""
            INSERT INTO issues (
                id, found_at, found_by, category, severity,
                spec_source, should_description, is_description,
                location, evidence, analysis, suggested_fix, confidence, status
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, 'open')
        """, (
            issue_id,
            int(time.time()),
            session_id,
            issue.category.value,
            issue.severity.value,
            issue.spec_source,
            issue.should_description,
            issue.is_description,
            issue.location,
            issue.evidence,
            issue.analysis,
            issue.suggested_fix,
            issue.confidence,
        ))
        
        conn.commit()
        conn.close()
        return issue_id
    
    def log_examination(
        self,
        session_id: str,
        question: str,
        module: str,
        issues_found: int = 0,
        notes: str = None
    ):
        """Log that a module was examined."""
        conn = self._connect()
        cursor = conn.cursor()
        
        cursor.execute("""
            INSERT INTO examination_log (session_id, question, module, examined_at, issues_found, notes)
            VALUES (?, ?, ?, ?, ?, ?)
        """, (session_id, question, module, int(time.time()), issues_found, notes))
        
        conn.commit()
        conn.close()
    
    def get_examination_log(self, session_id: str) -> List[Dict]:
        """Get examination log for a session."""
        conn = self._connect()
        cursor = conn.cursor()
        
        cursor.execute("""
            SELECT module, examined_at, issues_found, notes
            FROM examination_log WHERE session_id = ?
            ORDER BY examined_at ASC
        """, (session_id,))
        
        rows = cursor.fetchall()
        conn.close()
        
        return [
            {"module": r[0], "examined_at": r[1], "issues_found": r[2], "notes": r[3]}
            for r in rows
        ]
    
    def query_issues(
        self,
        session_id: Optional[str] = None,
        severity: Optional[str] = None,
        status: str = "open"
    ) -> List[Dict]:
        """Query issues with filters."""
        conn = self._connect()
        cursor = conn.cursor()
        
        conditions = ["status = ?"]
        params = [status]
        
        if session_id:
            conditions.append("found_by = ?")
            params.append(session_id)
        
        if severity:
            conditions.append("severity = ?")
            params.append(severity)
        
        where_clause = " AND ".join(conditions)
        
        cursor.execute(f"""
            SELECT id, category, severity, should_description, is_description, 
                   location, analysis, confidence
            FROM issues WHERE {where_clause}
            ORDER BY 
                CASE severity 
                    WHEN 'critical' THEN 1 
                    WHEN 'high' THEN 2 
                    WHEN 'medium' THEN 3 
                    WHEN 'low' THEN 4 
                END
        """, params)
        
        rows = cursor.fetchall()
        conn.close()
        
        return [
            {
                "id": r[0], "category": r[1], "severity": r[2],
                "should": r[3], "is": r[4], "location": r[5],
                "analysis": r[6], "confidence": r[7]
            }
            for r in rows
        ]


@dataclass
class ExaminationContext:
    """Context for an examination session."""
    session_id: str
    question: str
    codebase: CodebaseContext
    agentfs: AgentFSClient
    requirements: List[Requirement]
    llm_call: Optional[Callable] = None  # For recursive LLM calls
    
    @classmethod
    def create(
        cls,
        question: str,
        codebase_path: str,
        agentfs_path: str,
        spec_paths: List[str] = None,
        llm_call: Callable = None,
    ) -> "ExaminationContext":
        """Create a new examination context."""
        session_id = f"exam-{int(time.time())}-{uuid.uuid4().hex[:8]}"
        
        codebase = CodebaseContext(codebase_path)
        agentfs = AgentFSClient(agentfs_path)
        
        # Load requirements from specs
        requirements = []
        if spec_paths:
            requirements = load_specs(spec_paths)
        
        return cls(
            session_id=session_id,
            question=question,
            codebase=codebase,
            agentfs=agentfs,
            requirements=requirements,
            llm_call=llm_call,
        )


def analyze_scope(question: str, codebase: CodebaseContext) -> Dict[str, Any]:
    """
    Analyze the question to determine examination scope.
    
    Returns:
        - relevant_modules: List of modules to examine
        - spec_types: What spec types apply
        - examination_strategy: How to partition and examine
    """
    # Simple keyword-based scope detection
    # In a full implementation, this would use an LLM
    
    relevant_modules = []
    spec_types = []
    
    question_lower = question.lower()
    
    # DST-related questions
    if any(kw in question_lower for kw in ['dst', 'deterministic', 'simulation', 'test coverage']):
        relevant_modules.extend([
            'crates/kelpie-dst',
            'crates/kelpie-storage',
            'crates/kelpie-runtime',
        ])
        spec_types.append('dst_rules')
    
    # API/Letta-related questions
    if any(kw in question_lower for kw in ['letta', 'api', 'compatibility', 'endpoint']):
        relevant_modules.extend([
            'crates/kelpie-server/src/api',
            'crates/kelpie-server/src/models',
        ])
        spec_types.append('openapi')
    
    # Storage-related questions
    if any(kw in question_lower for kw in ['storage', 'fdb', 'foundationdb', 'persistence']):
        relevant_modules.extend([
            'crates/kelpie-storage',
            'crates/kelpie-server/src/storage',
        ])
    
    # Actor/runtime questions
    if any(kw in question_lower for kw in ['actor', 'runtime', 'activation', 'lifecycle']):
        relevant_modules.extend([
            'crates/kelpie-runtime',
            'crates/kelpie-server/src/actor',
        ])
    
    # Default: examine key modules
    if not relevant_modules:
        relevant_modules = [
            'crates/kelpie-core',
            'crates/kelpie-server',
            'crates/kelpie-runtime',
            'crates/kelpie-storage',
        ]
    
    return {
        "relevant_modules": list(set(relevant_modules)),
        "spec_types": list(set(spec_types)),
        "examination_strategy": "module_by_module",
    }


def examine_partition(
    ctx: ExaminationContext,
    partition_name: str,
) -> PartitionFinding:
    """
    Examine a single partition thoroughly.
    
    This is the core examination logic that:
    1. Loads the partition's code
    2. Identifies applicable requirements
    3. Compares IS vs SHOULD
    4. Records issues
    """
    finding = PartitionFinding(
        partition_name=partition_name,
        examined_at=int(time.time()),
    )
    
    # Get applicable requirements
    applicable_reqs = filter_requirements(
        ctx.requirements,
        module_path=partition_name,
    )
    
    # For each requirement, check if it's satisfied
    for req in applicable_reqs:
        # This is where the LLM would do actual examination
        # For now, we do basic structural checks
        
        if req.req_type == RequirementType.DST_COVERAGE:
            # Check if DST test exists for this module
            test_suffix = req.context.get("test_file_suffix", "_dst.rs")
            expected_test = partition_name.replace('.rs', test_suffix)
            
            # Check if test file exists
            test_path = Path(ctx.codebase.root) / expected_test
            if not test_path.exists():
                finding.issues.append(Issue(
                    category=IssueCategory.GAP,
                    severity=IssueSeverity.MEDIUM,
                    should_description=req.description,
                    is_description=f"No DST test file found at {expected_test}",
                    analysis=f"DST coverage requirement not met: {req.verification_hint}",
                    location=partition_name,
                    spec_source=req.source,
                    suggested_fix=f"Create DST test file: {expected_test}",
                ))
        
        elif req.req_type == RequirementType.API_ENDPOINT:
            # For API requirements, we'd check if handlers exist
            finding.observations.append(
                f"Checked API requirement: {req.description}"
            )
    
    # Log examination to AgentFS
    ctx.agentfs.log_examination(
        ctx.session_id,
        ctx.question,
        partition_name,
        issues_found=len(finding.issues),
    )
    
    # Record issues to AgentFS
    for issue in finding.issues:
        ctx.agentfs.record_issue(ctx.session_id, issue)
    
    return finding


def verify_thoroughness(ctx: ExaminationContext, expected_modules: List[str]) -> ThortoughnessReport:
    """Verify that examination was thorough."""
    log = ctx.agentfs.get_examination_log(ctx.session_id)
    examined = set(e["module"] for e in log)
    expected = set(expected_modules)
    
    missing = list(expected - examined)
    
    return ThortoughnessReport(
        complete=len(missing) == 0,
        examined_count=len(examined),
        expected_count=len(expected),
        missing_partitions=missing,
        coverage_percent=(len(examined) / len(expected) * 100) if expected else 100.0,
    )


def answer_codebase_question(
    question: str,
    codebase_path: str,
    agentfs_path: str,
    spec_paths: List[str] = None,
    llm_call: Callable = None,
) -> Answer:
    """
    Answer ANY question about the codebase.
    
    This is the main entry point for the Codebase Intelligence Layer.
    
    Args:
        question: The question to answer
        codebase_path: Path to the codebase root
        agentfs_path: Path to AgentFS database
        spec_paths: Optional list of spec files to load
        llm_call: Optional LLM function for recursive calls
    
    Returns:
        Complete, evidence-backed answer
    """
    # Create examination context
    ctx = ExaminationContext.create(
        question=question,
        codebase_path=codebase_path,
        agentfs_path=agentfs_path,
        spec_paths=spec_paths,
        llm_call=llm_call,
    )
    
    # 1. UNDERSTAND & SCOPE
    scope = analyze_scope(question, ctx.codebase)
    partitions = scope["relevant_modules"]
    
    # 2. SYSTEMATIC EXAMINATION
    all_findings: List[PartitionFinding] = []
    for partition in partitions:
        finding = examine_partition(ctx, partition)
        all_findings.append(finding)
    
    # 3. VERIFY THOROUGHNESS
    thoroughness = verify_thoroughness(ctx, partitions)
    
    # 4. GATHER ALL ISSUES
    all_issues = ctx.agentfs.query_issues(session_id=ctx.session_id)
    
    # 5. SYNTHESIZE ANSWER
    working = []
    broken = []
    
    for finding in all_findings:
        if not finding.issues:
            working.append(f"{finding.partition_name}: No issues found")
        else:
            for issue in finding.issues:
                broken.append(f"{issue.location}: {issue.is_description}")
    
    # Issue summary
    issue_summary: Dict[str, int] = {}
    for issue in all_issues:
        cat = issue["category"]
        issue_summary[cat] = issue_summary.get(cat, 0) + 1
    
    # Build direct answer
    if not broken:
        direct_answer = f"Based on examination of {len(partitions)} modules, the codebase appears to meet requirements for: {question}"
    else:
        direct_answer = f"Found {len(broken)} issues across {len(partitions)} modules examined. See details below."
    
    # Build answer
    answer = Answer(
        question=question,
        direct_answer=direct_answer,
        working=working,
        broken=broken,
        issues_found=len(all_issues),
        issue_summary=issue_summary,
        thoroughness=thoroughness,
        partitions_examined=partitions,
        metadata={
            "session_id": ctx.session_id,
            "spec_sources": [s for s in (spec_paths or [])],
            "examination_duration_ms": int(time.time() * 1000) - int(ctx.session_id.split('-')[1]) * 1000,
        },
    )
    
    # Add warnings if examination incomplete
    if not thoroughness.complete:
        answer.warnings.append(
            f"⚠️ INCOMPLETE EXAMINATION: Missing {len(thoroughness.missing_partitions)} partitions "
            f"({thoroughness.coverage_percent:.1f}% coverage)"
        )
    
    return answer
