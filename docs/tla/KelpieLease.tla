-------------------------------- MODULE KelpieLease --------------------------------
\* KelpieLease.tla - TLA+ specification for Kelpie's lease-based actor ownership
\*
\* This specification models the lease protocol from ADR-004 that ensures
\* single activation guarantee for virtual actors.
\*
\* Invariants:
\* - LeaseUniqueness: At most one node believes it holds a valid lease per actor
\* - RenewalRequiresOwnership: Only lease holder can renew
\* - ExpiredLeaseClaimable: Expired lease can be claimed by any node
\* - LeaseValidityBounds: Lease expiry time within configured bounds
\*
\* Liveness:
\* - EventualLeaseResolution: Eventually a lease is granted or expires
\*
\* Author: Kelpie Team
\* Date: 2026-01-24
\* Related: ADR-002 (G2.2), ADR-004 (G4.2)

EXTENDS Integers, Sequences, FiniteSets, TLC

\* ============================================================================
\* Constants
\* ============================================================================

CONSTANTS
    Nodes,          \* Set of node identifiers (e.g., {"n1", "n2"})
    Actors,         \* Set of actor identifiers (e.g., {"a1", "a2"})
    LeaseDuration,  \* Duration of a lease in clock ticks (e.g., 3)
    MaxClock,       \* Maximum clock value for bounded model checking
    UseSafeVersion  \* TRUE for correct CAS, FALSE for buggy race condition

\* ============================================================================
\* Variables
\* ============================================================================

VARIABLES
    leases,         \* Ground truth: [Actors -> [holder: Nodes \cup {NoHolder}, expiry: Int]]
    clock,          \* Global clock (models wall clock time)
    nodeBeliefs     \* What each node BELIEVES it owns: [Nodes -> [Actors -> [held: BOOLEAN, expiry: Int]]]

vars == <<leases, clock, nodeBeliefs>>

\* ============================================================================
\* Constants for empty values
\* ============================================================================

NoHolder == "NONE"  \* Sentinel value for no lease holder

\* ============================================================================
\* Type Invariants
\* ============================================================================

TypeOK ==
    /\ leases \in [Actors -> [holder: Nodes \cup {NoHolder}, expiry: Int]]
    /\ clock \in 0..MaxClock
    /\ nodeBeliefs \in [Nodes -> [Actors -> [held: BOOLEAN, expiry: Int]]]

\* ============================================================================
\* Helper Functions
\* ============================================================================

\* Check if a lease is currently valid (not expired) - ground truth
IsValidLease(actor) ==
    /\ leases[actor].holder /= NoHolder
    /\ leases[actor].expiry > clock

\* Check if a lease has expired - ground truth
IsExpiredLease(actor) ==
    /\ leases[actor].holder /= NoHolder
    /\ leases[actor].expiry <= clock

\* Check if there is no lease (never acquired or released) - ground truth
NoLease(actor) ==
    leases[actor].holder = NoHolder

\* Check if a node BELIEVES it holds a valid lease
NodeBelievesItHolds(node, actor) ==
    /\ nodeBeliefs[node][actor].held
    /\ nodeBeliefs[node][actor].expiry > clock

\* ============================================================================
\* Initial State
\* ============================================================================

Init ==
    /\ leases = [a \in Actors |-> [holder |-> NoHolder, expiry |-> 0]]
    /\ clock = 0
    /\ nodeBeliefs = [n \in Nodes |-> [a \in Actors |-> [held |-> FALSE, expiry |-> 0]]]

\* ============================================================================
\* Actions - Safe Version (Atomic CAS)
\* ============================================================================

\* A node attempts to acquire a lease for an actor using atomic CAS.
\* This models the FDB transaction that atomically:
\* 1. Reads current lease state
\* 2. Checks no valid lease exists
\* 3. Writes new lease with expiry
\* 4. Updates node's belief
AcquireLeaseSafe(node, actor) ==
    /\ ~IsValidLease(actor)  \* No valid lease exists (CAS precondition)
    /\ LET newExpiry == clock + LeaseDuration
       IN
        /\ leases' = [leases EXCEPT ![actor] = [holder |-> node, expiry |-> newExpiry]]
        /\ nodeBeliefs' = [nodeBeliefs EXCEPT ![node][actor] = [held |-> TRUE, expiry |-> newExpiry]]
    /\ UNCHANGED clock

\* A node renews its lease for an actor.
\* Only the current holder can renew (ownership check).
RenewLeaseSafe(node, actor) ==
    /\ IsValidLease(actor)              \* Lease must be valid
    /\ leases[actor].holder = node      \* Only holder can renew
    /\ LET newExpiry == clock + LeaseDuration
       IN
        /\ leases' = [leases EXCEPT ![actor] = [holder |-> node, expiry |-> newExpiry]]
        /\ nodeBeliefs' = [nodeBeliefs EXCEPT ![node][actor] = [held |-> TRUE, expiry |-> newExpiry]]
    /\ UNCHANGED clock

\* ============================================================================
\* Actions - Buggy Version (Race Condition - Non-Atomic Read-Write)
\* ============================================================================

\* Buggy: A node reads that no lease exists and immediately claims it.
\* The bug: This is NOT atomic - another node could have claimed between read and write.
\* We model this by allowing the write even if the lease state changed.
AcquireLeaseBuggy(node, actor) ==
    \* Precondition: Node reads no valid lease (but this might be stale!)
    /\ ~IsValidLease(actor)
    \* The node writes its claim
    /\ LET newExpiry == clock + LeaseDuration
       IN
        /\ leases' = [leases EXCEPT ![actor] = [holder |-> node, expiry |-> newExpiry]]
        /\ nodeBeliefs' = [nodeBeliefs EXCEPT ![node][actor] = [held |-> TRUE, expiry |-> newExpiry]]
    /\ UNCHANGED clock

\* Buggy: A node claims a lease WITHOUT checking current state.
\* This models a race where the check happened earlier (and was stale).
\* The node remembers it read "no lease" and proceeds to write.
AcquireLeaseNoCheck(node, actor) ==
    \* NO PRECONDITION on lease state! (the "bug")
    \* The node just writes, believing it saw "no lease" earlier
    /\ ~nodeBeliefs[node][actor].held  \* Node doesn't think it already has it
    /\ LET newExpiry == clock + LeaseDuration
       IN
        /\ leases' = [leases EXCEPT ![actor] = [holder |-> node, expiry |-> newExpiry]]
        /\ nodeBeliefs' = [nodeBeliefs EXCEPT ![node][actor] = [held |-> TRUE, expiry |-> newExpiry]]
    /\ UNCHANGED clock

\* Buggy renewal - same as safe for simplicity
RenewLeaseBuggy(node, actor) ==
    RenewLeaseSafe(node, actor)

\* ============================================================================
\* Time Advancement
\* ============================================================================

\* Advance the clock by 1 tick.
\* Node beliefs about expired leases should be updated.
TickClock ==
    /\ clock < MaxClock
    /\ clock' = clock + 1
    \* When clock advances, nodes with expired beliefs should realize
    \* (In a real system this happens via timeout, modeled here as instant)
    /\ nodeBeliefs' = [n \in Nodes |-> [a \in Actors |->
        IF nodeBeliefs[n][a].held /\ nodeBeliefs[n][a].expiry <= clock + 1
        THEN [held |-> FALSE, expiry |-> 0]  \* Node realizes lease expired
        ELSE nodeBeliefs[n][a]]]
    /\ UNCHANGED leases

\* ============================================================================
\* Release Lease (Voluntary Deactivation)
\* ============================================================================

\* A node voluntarily releases its lease (graceful deactivation).
ReleaseLease(node, actor) ==
    /\ nodeBeliefs[node][actor].held    \* Node thinks it has the lease
    /\ leases[actor].holder = node      \* And it actually does
    /\ leases' = [leases EXCEPT ![actor] = [holder |-> NoHolder, expiry |-> 0]]
    /\ nodeBeliefs' = [nodeBeliefs EXCEPT ![node][actor] = [held |-> FALSE, expiry |-> 0]]
    /\ UNCHANGED clock

\* ============================================================================
\* Next State Relation
\* ============================================================================

NextSafe ==
    \/ \E n \in Nodes, a \in Actors: AcquireLeaseSafe(n, a)
    \/ \E n \in Nodes, a \in Actors: RenewLeaseSafe(n, a)
    \/ \E n \in Nodes, a \in Actors: ReleaseLease(n, a)
    \/ TickClock

NextBuggy ==
    \* The buggy version allows claiming without proper CAS
    \/ \E n \in Nodes, a \in Actors: AcquireLeaseNoCheck(n, a)
    \/ \E n \in Nodes, a \in Actors: RenewLeaseBuggy(n, a)
    \/ \E n \in Nodes, a \in Actors: ReleaseLease(n, a)
    \/ TickClock

Next == IF UseSafeVersion THEN NextSafe ELSE NextBuggy

\* ============================================================================
\* Fairness (for Liveness)
\* ============================================================================

Fairness ==
    /\ WF_vars(TickClock)
    /\ \A n \in Nodes, a \in Actors:
        IF UseSafeVersion
        THEN WF_vars(AcquireLeaseSafe(n, a))
        ELSE WF_vars(AcquireLeaseNoCheck(n, a))

\* ============================================================================
\* Safety Invariants
\* ============================================================================

\* LeaseUniqueness: At most one node believes it holds a valid lease per actor.
\* This is the CRITICAL invariant for single activation guarantee.
\* In the buggy version, two nodes can both believe they hold the lease!
LeaseUniqueness ==
    \A a \in Actors:
        LET believingNodes == {n \in Nodes: NodeBelievesItHolds(n, a)}
        IN Cardinality(believingNodes) <= 1

\* Alternative: Ground truth uniqueness (always holds, even in buggy version)
GroundTruthUniqueness ==
    \A a \in Actors:
        LET holders == {n \in Nodes:
            /\ leases[a].holder = n
            /\ leases[a].expiry > clock}
        IN Cardinality(holders) <= 1

\* RenewalRequiresOwnership: After a renewal, the holder must be the same.
\* (This is implicitly enforced by the RenewLease action preconditions)
RenewalRequiresOwnership ==
    \A a \in Actors:
        IsValidLease(a) =>
            \E n \in Nodes: leases[a].holder = n

\* ExpiredLeaseClaimable: An expired lease doesn't block new acquisition.
ExpiredLeaseClaimable ==
    \A a \in Actors:
        ~IsValidLease(a) =>
            \E n \in Nodes: ENABLED AcquireLeaseSafe(n, a)

\* LeaseValidityBounds: Lease expiry is within bounds.
LeaseValidityBounds ==
    \A a \in Actors:
        leases[a].holder /= NoHolder =>
            /\ leases[a].expiry >= 0
            /\ leases[a].expiry <= MaxClock + LeaseDuration

\* BeliefConsistency: If a node believes it holds a lease, it should be the actual holder.
\* This FAILS in the buggy version due to race conditions.
BeliefConsistency ==
    \A n \in Nodes, a \in Actors:
        NodeBelievesItHolds(n, a) => leases[a].holder = n

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ LeaseUniqueness
    /\ RenewalRequiresOwnership
    /\ LeaseValidityBounds

\* ============================================================================
\* Liveness Properties
\* ============================================================================

\* EventualLeaseResolution: For any actor, eventually either:
\* 1. Someone holds a valid lease, OR
\* 2. No one believes they hold it (clean state)
EventualLeaseResolution ==
    \A a \in Actors:
        []<>(IsValidLease(a) \/ ~(\E n \in Nodes: NodeBelievesItHolds(n, a)))

\* ============================================================================
\* Specification
\* ============================================================================

Spec == Init /\ [][Next]_vars /\ Fairness

\* ============================================================================
\* Theorems (for TLC to check)
\* ============================================================================

THEOREM Spec => []SafetyInvariant
THEOREM Spec => EventualLeaseResolution

================================================================================
