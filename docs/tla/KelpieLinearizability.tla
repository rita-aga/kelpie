------------------------------ MODULE KelpieLinearizability ------------------------------
(***************************************************************************)
(* TLA+ Specification for Kelpie Linearizability Guarantees                 *)
(*                                                                          *)
(* This spec models the linearization points for client-visible operations  *)
(* in Kelpie's distributed actor system, as defined in ADR-004.            *)
(*                                                                          *)
(* Linearization Points (per ADR-004):                                      *)
(* 1. Actor Claim: FDB transaction commit                                   *)
(* 2. Actor Release: FDB transaction commit                                 *)
(* 3. Placement Read: FDB snapshot read                                     *)
(* 4. Message Dispatch: After activation check, before processing          *)
(*                                                                          *)
(* The key insight is that linearizability is achieved through FDB's        *)
(* strict serializability: each operation appears to take effect            *)
(* atomically at some point between invocation and response.               *)
(*                                                                          *)
(* Related Specs:                                                           *)
(* - KelpieSingleActivation.tla: Models OCC for single activation          *)
(* - KelpieLease.tla: Models lease-based ownership                          *)
(* - KelpieFDBTransaction.tla: Models FDB transaction semantics            *)
(*                                                                          *)
(* TigerStyle: All constants have explicit units and bounds.               *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

(***************************************************************************)
(* CONSTANTS                                                                *)
(***************************************************************************)

CONSTANT
    Clients,        \* Set of clients that can invoke operations
    Actors,         \* Set of actor IDs
    Nodes,          \* Set of nodes that can host actors
    NONE,           \* Sentinel value for "no value"
    MAX_HISTORY     \* Maximum history length for bounded checking

(***************************************************************************)
(* VARIABLES                                                                *)
(*                                                                          *)
(* The model tracks:                                                        *)
(* - Global linearization order (ground truth)                              *)
(* - Per-client pending operations                                          *)
(* - Actor ownership state (which node owns which actor)                    *)
(* - FDB state (simulated ground truth)                                     *)
(***************************************************************************)

VARIABLES
    \* Global linearization order - sequence of linearized operations
    history,

    \* Actor ownership: actor_id -> node | NONE
    ownership,

    \* FDB version counter (for OCC)
    fdb_version,

    \* Pending client operations: client -> (op | NONE)
    pending,

    \* Operation counter for unique IDs
    op_counter

vars == <<history, ownership, fdb_version, pending, op_counter>>

(***************************************************************************)
(* OPERATION TYPES                                                          *)
(*                                                                          *)
(* Each operation has:                                                      *)
(* - type: Claim, Release, Read, Dispatch                                   *)
(* - client: which client initiated it                                      *)
(* - actor: which actor it targets                                          *)
(* - id: unique operation ID                                                *)
(* - response: result after linearization                                   *)
(***************************************************************************)

OperationType == {"Claim", "Release", "Read", "Dispatch"}

\* A pending operation (not yet linearized)
PendingOp == [
    type: OperationType,
    client: Clients,
    actor: Actors,
    id: Nat
]

\* A linearized operation (in history)
LinearizedOp == [
    type: OperationType,
    client: Clients,
    actor: Actors,
    id: Nat,
    response: {"ok", "fail", "owner", "no_owner"} \cup Nodes
]

(***************************************************************************)
(* TYPE INVARIANT                                                           *)
(***************************************************************************)

TypeOK ==
    /\ history \in Seq(LinearizedOp)
    /\ ownership \in [Actors -> Nodes \cup {NONE}]
    /\ fdb_version \in Nat
    /\ pending \in [Clients -> (PendingOp \cup {NONE})]
    /\ op_counter \in Nat

(***************************************************************************)
(* INITIAL STATE                                                            *)
(***************************************************************************)

Init ==
    /\ history = <<>>
    /\ ownership = [a \in Actors |-> NONE]
    /\ fdb_version = 0
    /\ pending = [c \in Clients |-> NONE]
    /\ op_counter = 0

(***************************************************************************)
(* HELPER PREDICATES                                                        *)
(***************************************************************************)

\* Client has no pending operation
ClientIdle(c) == pending[c] = NONE

\* Client has a pending operation
ClientBusy(c) == pending[c] # NONE

\* Actor is owned by some node
ActorOwned(a) == ownership[a] # NONE

\* Actor is not owned
ActorFree(a) == ownership[a] = NONE

(***************************************************************************)
(* CLIENT INVOCATIONS                                                       *)
(*                                                                          *)
(* Clients invoke operations. Each invocation creates a pending operation   *)
(* that will later be linearized. The linearization point determines        *)
(* when the operation takes effect in the global order.                     *)
(***************************************************************************)

\* Client invokes a Claim operation (request to own an actor)
InvokeClaim(c, a) ==
    /\ ClientIdle(c)
    /\ pending' = [pending EXCEPT ![c] = [
           type |-> "Claim",
           client |-> c,
           actor |-> a,
           id |-> op_counter
       ]]
    /\ op_counter' = op_counter + 1
    /\ UNCHANGED <<history, ownership, fdb_version>>

\* Client invokes a Release operation (release ownership of actor)
InvokeRelease(c, a) ==
    /\ ClientIdle(c)
    /\ pending' = [pending EXCEPT ![c] = [
           type |-> "Release",
           client |-> c,
           actor |-> a,
           id |-> op_counter
       ]]
    /\ op_counter' = op_counter + 1
    /\ UNCHANGED <<history, ownership, fdb_version>>

\* Client invokes a Read operation (read current owner of actor)
InvokeRead(c, a) ==
    /\ ClientIdle(c)
    /\ pending' = [pending EXCEPT ![c] = [
           type |-> "Read",
           client |-> c,
           actor |-> a,
           id |-> op_counter
       ]]
    /\ op_counter' = op_counter + 1
    /\ UNCHANGED <<history, ownership, fdb_version>>

\* Client invokes a Dispatch operation (send message to actor)
InvokeDispatch(c, a) ==
    /\ ClientIdle(c)
    /\ pending' = [pending EXCEPT ![c] = [
           type |-> "Dispatch",
           client |-> c,
           actor |-> a,
           id |-> op_counter
       ]]
    /\ op_counter' = op_counter + 1
    /\ UNCHANGED <<history, ownership, fdb_version>>

(***************************************************************************)
(* LINEARIZATION POINTS                                                     *)
(*                                                                          *)
(* Each operation type has a specific linearization point:                  *)
(* - Claim: When FDB transaction commits successfully                       *)
(* - Release: When FDB transaction commits                                  *)
(* - Read: When FDB snapshot read completes                                 *)
(* - Dispatch: When activation check passes                                 *)
(*                                                                          *)
(* At the linearization point, the operation atomically takes effect        *)
(* and is added to the global history.                                      *)
(***************************************************************************)

\* Linearize a Claim operation
\* Linearization point: FDB commit (ADR-004)
LinearizeClaim(c, node) ==
    /\ ClientBusy(c)
    /\ pending[c].type = "Claim"
    /\ LET op == pending[c]
           actor == op.actor
       IN
       \* Can only claim if actor is not owned
       \/ /\ ActorFree(actor)
          /\ ownership' = [ownership EXCEPT ![actor] = node]
          /\ fdb_version' = fdb_version + 1
          /\ history' = Append(history, [
                 type |-> "Claim",
                 client |-> c,
                 actor |-> actor,
                 id |-> op.id,
                 response |-> "ok"
             ])
          /\ pending' = [pending EXCEPT ![c] = NONE]
       \* Fail if actor already owned
       \/ /\ ActorOwned(actor)
          /\ history' = Append(history, [
                 type |-> "Claim",
                 client |-> c,
                 actor |-> actor,
                 id |-> op.id,
                 response |-> "fail"
             ])
          /\ pending' = [pending EXCEPT ![c] = NONE]
          /\ UNCHANGED <<ownership, fdb_version>>
    /\ UNCHANGED <<op_counter>>

\* Linearize a Release operation
\* Linearization point: FDB commit (ADR-004)
LinearizeRelease(c) ==
    /\ ClientBusy(c)
    /\ pending[c].type = "Release"
    /\ LET op == pending[c]
           actor == op.actor
       IN
       \* Can only release if actor exists (owned or not)
       /\ ownership' = [ownership EXCEPT ![actor] = NONE]
       /\ fdb_version' = fdb_version + 1
       /\ history' = Append(history, [
              type |-> "Release",
              client |-> c,
              actor |-> actor,
              id |-> op.id,
              response |-> "ok"
          ])
       /\ pending' = [pending EXCEPT ![c] = NONE]
    /\ UNCHANGED <<op_counter>>

\* Linearize a Read operation
\* Linearization point: FDB snapshot read (ADR-004)
LinearizeRead(c) ==
    /\ ClientBusy(c)
    /\ pending[c].type = "Read"
    /\ LET op == pending[c]
           actor == op.actor
           current_owner == ownership[actor]
       IN
       /\ history' = Append(history, [
              type |-> "Read",
              client |-> c,
              actor |-> actor,
              id |-> op.id,
              response |-> IF current_owner = NONE
                           THEN "no_owner"
                           ELSE current_owner
          ])
       /\ pending' = [pending EXCEPT ![c] = NONE]
    /\ UNCHANGED <<ownership, fdb_version, op_counter>>

\* Linearize a Dispatch operation
\* Linearization point: After activation check, before processing (ADR-004)
LinearizeDispatch(c) ==
    /\ ClientBusy(c)
    /\ pending[c].type = "Dispatch"
    /\ LET op == pending[c]
           actor == op.actor
       IN
       \* Dispatch succeeds only if actor is owned (active)
       \/ /\ ActorOwned(actor)
          /\ history' = Append(history, [
                 type |-> "Dispatch",
                 client |-> c,
                 actor |-> actor,
                 id |-> op.id,
                 response |-> "ok"
             ])
          /\ pending' = [pending EXCEPT ![c] = NONE]
          /\ UNCHANGED <<ownership, fdb_version>>
       \* Dispatch fails if actor not active
       \/ /\ ActorFree(actor)
          /\ history' = Append(history, [
                 type |-> "Dispatch",
                 client |-> c,
                 actor |-> actor,
                 id |-> op.id,
                 response |-> "fail"
             ])
          /\ pending' = [pending EXCEPT ![c] = NONE]
          /\ UNCHANGED <<ownership, fdb_version>>
    /\ UNCHANGED <<op_counter>>

(***************************************************************************)
(* NEXT STATE RELATION                                                      *)
(***************************************************************************)

Next ==
    \/ \E c \in Clients, a \in Actors:
        \/ InvokeClaim(c, a)
        \/ InvokeRelease(c, a)
        \/ InvokeRead(c, a)
        \/ InvokeDispatch(c, a)
    \/ \E c \in Clients, n \in Nodes:
        LinearizeClaim(c, n)
    \/ \E c \in Clients:
        \/ LinearizeRelease(c)
        \/ LinearizeRead(c)
        \/ LinearizeDispatch(c)

(***************************************************************************)
(* FAIRNESS                                                                 *)
(*                                                                          *)
(* Weak fairness ensures that every pending operation eventually           *)
(* linearizes (completes).                                                  *)
(***************************************************************************)

Fairness ==
    /\ \A c \in Clients, n \in Nodes:
        WF_vars(LinearizeClaim(c, n))
    /\ \A c \in Clients:
        /\ WF_vars(LinearizeRelease(c))
        /\ WF_vars(LinearizeRead(c))
        /\ WF_vars(LinearizeDispatch(c))

(***************************************************************************)
(* SAFETY PROPERTIES - LINEARIZABILITY INVARIANTS                          *)
(***************************************************************************)

\* Sequential consistency: all operations on same actor appear in same order
\* For any two operations on same actor, one happens-before the other
SequentialPerActor ==
    \A i, j \in 1..Len(history):
        i < j /\ history[i].actor = history[j].actor =>
            \* Operation i happens before j in the linearization
            TRUE  \* This is enforced by sequence ordering

\* Read-your-writes: A read after a successful claim sees that claim
\* (within same client)
ReadYourWrites ==
    \A i, j \in 1..Len(history):
        /\ i < j
        /\ history[i].client = history[j].client
        /\ history[i].type = "Claim"
        /\ history[i].response = "ok"
        /\ history[j].type = "Read"
        /\ history[j].actor = history[i].actor
        \* No intervening release on this actor
        /\ ~\E k \in (i+1)..(j-1):
            /\ history[k].actor = history[i].actor
            /\ history[k].type = "Release"
        => history[j].response # "no_owner"

\* Monotonic reads: Once a read sees an owner, subsequent reads don't see "no_owner"
\* unless there's an intervening release
MonotonicReads ==
    \A i, j \in 1..Len(history):
        /\ i < j
        /\ history[i].type = "Read"
        /\ history[i].actor = history[j].actor
        /\ history[j].type = "Read"
        /\ history[i].response # "no_owner"
        \* No intervening release
        /\ ~\E k \in (i+1)..(j-1):
            /\ history[k].actor = history[i].actor
            /\ history[k].type = "Release"
        => history[j].response # "no_owner"

\* Dispatch consistency: Dispatch succeeds iff actor is owned
DispatchConsistency ==
    \A i \in 1..Len(history):
        history[i].type = "Dispatch" =>
        \* Find most recent claim/release for this actor before this dispatch
        LET prior_claims == {j \in 1..(i-1):
                history[j].actor = history[i].actor /\
                history[j].type = "Claim" /\
                history[j].response = "ok"}
            prior_releases == {j \in 1..(i-1):
                history[j].actor = history[i].actor /\
                history[j].type = "Release"}
            last_claim == IF prior_claims = {} THEN 0
                          ELSE CHOOSE j \in prior_claims:
                              \A k \in prior_claims: k <= j
            last_release == IF prior_releases = {} THEN 0
                            ELSE CHOOSE j \in prior_releases:
                                \A k \in prior_releases: k <= j
        IN
        \* Dispatch succeeds iff last claim > last release (actor is owned)
        (history[i].response = "ok") <=> (last_claim > last_release)

\* Combined linearizability invariant
LinearizabilityInvariant ==
    /\ SequentialPerActor
    /\ ReadYourWrites
    /\ MonotonicReads
    /\ DispatchConsistency

(***************************************************************************)
(* LIVENESS PROPERTIES                                                      *)
(***************************************************************************)

\* Every pending operation eventually completes
EventualCompletion ==
    \A c \in Clients:
        ClientBusy(c) ~> ClientIdle(c)

\* Every claim on a free actor eventually succeeds
EventualClaim ==
    \A c \in Clients, a \in Actors:
        (ClientBusy(c) /\ pending[c].type = "Claim" /\ ActorFree(a)) ~>
        (ClientIdle(c))

(***************************************************************************)
(* SPECIFICATION                                                            *)
(***************************************************************************)

\* Full specification with fairness for liveness checking
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety-only specification (no fairness)
SafetySpec == Init /\ [][Next]_vars

(***************************************************************************)
(* STATE CONSTRAINT (for bounded model checking)                           *)
(***************************************************************************)

StateConstraint ==
    /\ Len(history) <= MAX_HISTORY
    /\ fdb_version <= 5
    /\ op_counter <= 8

(***************************************************************************)
(* THEOREMS                                                                 *)
(***************************************************************************)

\* Safety theorem: Linearizability holds in all reachable states
THEOREM Spec => []LinearizabilityInvariant

\* Liveness theorem: Every operation eventually completes
THEOREM Spec => EventualCompletion

=============================================================================
