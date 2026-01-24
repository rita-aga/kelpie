--------------------------- MODULE KelpieActorLifecycle ---------------------------
(***************************************************************************)
(* TLA+ Specification for Kelpie Actor Lifecycle Management                *)
(*                                                                         *)
(* Models the lifecycle of a virtual actor in Kelpie, verifying:           *)
(* - G1.3: Lifecycle ordering (activate -> invoke -> deactivate)           *)
(* - G1.5: Automatic deactivation after idle timeout                       *)
(*                                                                         *)
(* Reference: ADR-001 Virtual Actor Model                                  *)
(* Implementation: crates/kelpie-runtime/src/activation.rs                 *)
(***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANTS
    MAX_PENDING,      \* Maximum concurrent invocations
    IDLE_TIMEOUT,     \* Ticks before idle deactivation
    BUGGY             \* TRUE enables buggy behavior for testing

(***************************************************************************)
(* State Variables                                                         *)
(***************************************************************************)

VARIABLES
    state,            \* Actor lifecycle state: "Inactive", "Activating", "Active", "Deactivating"
    pending,          \* Number of pending invocations (0..MAX_PENDING)
    idleTicks         \* Ticks since last activity (for idle timeout)

vars == <<state, pending, idleTicks>>

(***************************************************************************)
(* Type Invariant                                                          *)
(***************************************************************************)

TypeOK ==
    /\ state \in {"Inactive", "Activating", "Active", "Deactivating"}
    /\ pending \in 0..MAX_PENDING
    /\ idleTicks \in 0..(IDLE_TIMEOUT + 1)

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)

Init ==
    /\ state = "Inactive"
    /\ pending = 0
    /\ idleTicks = 0

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Activate: Transition from Inactive to Activating, then to Active
\* Models: ActiveActor::activate() in activation.rs
Activate ==
    /\ state = "Inactive"
    /\ state' = "Activating"
    /\ pending' = pending
    /\ idleTicks' = 0

\* Complete activation: Transition from Activating to Active
\* Models: on_activate hook completion
CompleteActivation ==
    /\ state = "Activating"
    /\ state' = "Active"
    /\ pending' = pending
    /\ idleTicks' = 0

\* Start an invocation: Increment pending counter
\* Models: DispatcherHandle::invoke() accepting a request
\* Safe: Requires state = Active
\* Buggy: Allows invoke in any state (violates G1.3)
StartInvoke ==
    /\ pending < MAX_PENDING
    /\ IF BUGGY
       THEN TRUE  \* Buggy: Allow invoke in any state
       ELSE state = "Active"  \* Safe: Only invoke when Active
    /\ pending' = pending + 1
    /\ idleTicks' = 0  \* Reset idle timer on activity
    /\ state' = state

\* Complete an invocation: Decrement pending counter
\* Models: process_invocation() completing
CompleteInvoke ==
    /\ pending > 0
    /\ pending' = pending - 1
    /\ idleTicks' = 0  \* Reset idle timer on activity
    /\ state' = state

\* Idle tick: Increment idle timer when no activity
\* Models: Time passing without invocations
IdleTick ==
    /\ state = "Active"
    /\ pending = 0  \* Only tick when no pending invocations
    /\ idleTicks < IDLE_TIMEOUT + 1
    /\ idleTicks' = idleTicks + 1
    /\ state' = state
    /\ pending' = pending

\* Start deactivation: Transition to Deactivating when idle timeout reached
\* Models: should_deactivate() returning true
\* Precondition: Must be Active with no pending invocations
StartDeactivate ==
    /\ state = "Active"
    /\ pending = 0  \* Graceful: Wait for invocations to complete
    /\ idleTicks >= IDLE_TIMEOUT
    /\ state' = "Deactivating"
    /\ pending' = pending
    /\ idleTicks' = idleTicks

\* Complete deactivation: Transition to Inactive
\* Models: deactivate() completing (on_deactivate + state persistence)
CompleteDeactivate ==
    /\ state = "Deactivating"
    /\ state' = "Inactive"
    /\ pending' = 0
    /\ idleTicks' = 0

(***************************************************************************)
(* Next State Relation                                                     *)
(***************************************************************************)

Next ==
    \/ Activate
    \/ CompleteActivation
    \/ StartInvoke
    \/ CompleteInvoke
    \/ IdleTick
    \/ StartDeactivate
    \/ CompleteDeactivate

(***************************************************************************)
(* Fairness (for liveness properties)                                      *)
(***************************************************************************)

\* Weak fairness: If an action is continuously enabled, it eventually happens
\* Strong fairness: If an action is infinitely often enabled, it eventually happens
\* We use SF for StartDeactivate because invocations may interrupt the idle period,
\* but if the actor keeps becoming eligible for deactivation, it should eventually happen.
Fairness ==
    /\ WF_vars(CompleteActivation)
    /\ WF_vars(CompleteInvoke)
    /\ WF_vars(IdleTick)
    /\ SF_vars(StartDeactivate)  \* Strong fairness: fires even if only intermittently enabled
    /\ WF_vars(CompleteDeactivate)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

\* LifecycleOrdering: No invoke without activate (G1.3)
\* Invocations can only happen when the actor is Active
\* In buggy mode, this can be violated
LifecycleOrdering ==
    pending > 0 => state = "Active"

\* GracefulDeactivation: Active invocations complete before deactivate (G1.3)
\* Cannot be in Deactivating state with pending invocations
GracefulDeactivation ==
    state = "Deactivating" => pending = 0

\* IdleTimeoutRespected: Cannot deactivate before timeout
\* Only start deactivation after idle timeout is reached
IdleTimeoutRespected ==
    state = "Deactivating" => idleTicks >= IDLE_TIMEOUT

\* NoInvokeWhileDeactivating: Cannot start new invocations during deactivation
NoInvokeWhileDeactivating ==
    state = "Deactivating" => pending = 0

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

\* EventualDeactivation: If actor reaches idle timeout, it eventually deactivates
\* This models G1.5: Automatic deactivation after idle timeout
\* Note: We check when idleTicks reaches timeout, not just when pending=0,
\* because new invocations can arrive and reset the idle timer.
EventualDeactivation ==
    (state = "Active" /\ idleTicks >= IDLE_TIMEOUT) ~> (state = "Inactive")

\* EventualActivation: If activation starts, it eventually completes
EventualActivation ==
    (state = "Activating") ~> (state = "Active" \/ state = "Inactive")

\* EventualInvocationCompletion: Started invocations eventually complete
EventualInvocationCompletion ==
    (pending > 0) ~> (pending = 0)

(***************************************************************************)
(* Composite Properties                                                    *)
(***************************************************************************)

\* All safety invariants combined
Safety == TypeOK /\ LifecycleOrdering /\ GracefulDeactivation /\ IdleTimeoutRespected

\* All liveness properties combined
Liveness == EventualDeactivation /\ EventualActivation /\ EventualInvocationCompletion

=============================================================================
\* Modification History
\* Created 2026-01-24 by Claude for Kelpie project
\* Reference: GitHub Issue #8
