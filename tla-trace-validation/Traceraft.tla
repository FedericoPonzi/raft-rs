------------------------------- MODULE Traceraft -------------------------------
\* Trace validation for raft-rs against the Raft safety invariants.
\*
\* Reads ndjson traces produced by the randomized tests in
\* harness/tests/trace_validation.rs and checks Raft safety properties
\* on every observed state snapshot.
\*
\* Methodology follows "Smart Casual Verification of the Confidential
\* Consortium Framework" (NSDI'25).

EXTENDS Naturals, FiniteSets, Sequences, TLC, Json, IOUtils

\* -------------------------------------------------------------------------
\* Trace loading
\* -------------------------------------------------------------------------

ASSUME TLCGet("config").mode = "bfs"
ASSUME TLCGet("config").worker = 1

JsonFile ==
    IF "RAFT_TRACE" \in DOMAIN IOEnv THEN IOEnv.RAFT_TRACE
    ELSE "traces/rand3n_0.ndjson"

JsonLog == ndJsonDeserialize(JsonFile)

TraceLog ==
    SelectSeq(JsonLog, LAMBDA entry: entry.tag = "raft_trace")

ASSUME TLCEval(Print(<<"Trace:", JsonFile, "Length:", Len(TraceLog)>>, TRUE))

\* -------------------------------------------------------------------------
\* Constants and helpers
\* -------------------------------------------------------------------------

CONSTANTS NodeOne, NodeTwo, NodeThree, NodeFour, NodeFive
CONSTANTS Follower, Candidate, Leader

\* Determine server set from the first trace entry.
TraceNodeIds == DOMAIN TraceLog[1].state

Server ==
    IF Cardinality(TraceNodeIds) = 5
    THEN {NodeOne, NodeTwo, NodeThree, NodeFour, NodeFive}
    ELSE {NodeOne, NodeTwo, NodeThree}

Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* -------------------------------------------------------------------------
\* Trace state machine
\* -------------------------------------------------------------------------

VARIABLE l

logline == TraceLog[l]

NodeState(i) == logline.state[ToString(i)]
NodeTerm(i) == NodeState(i).currentTerm
NodeRole(i) == NodeState(i).state
NodeLog(i) == NodeState(i).log
NodeCommitIndex(i) == NodeState(i).commitIndex

TraceInit ==
    /\ l = 1
    /\ TraceLog[1].action = "Init"

TraceNext ==
    /\ l < Len(TraceLog)
    /\ l' = l + 1

TraceSpec == TraceInit /\ [][TraceNext]_<<l>>

TraceView == <<l>>

Termination == l = Len(TraceLog) => TLCSet("exit", TRUE)

TraceMatched ==
    [](l <= Len(TraceLog) =>
        [](TLCGet("queue") \in Nat \ {0} \/ l >= Len(TraceLog)))

TraceMatchedNonTrivially == TLCGet("stats").diameter >= 2

\* -------------------------------------------------------------------------
\* Raft safety invariants (Raft paper §5)
\* -------------------------------------------------------------------------

\* §5.2  At most one leader per term.
ElectionSafetyInv ==
    \A i, j \in Server :
        (/\ NodeRole(i) = "Leader"
         /\ NodeRole(j) = "Leader"
         /\ NodeTerm(i) = NodeTerm(j))
        => i = j

\* §5.3  If two logs contain an entry with the same index and term,
\*       then the logs are identical in all preceding entries.
LogMatchingInv ==
    \A i, j \in Server :
        \A k \in 1..Min({Len(NodeLog(i)), Len(NodeLog(j))}) :
            NodeLog(i)[k].term = NodeLog(j)[k].term
            => \A m \in 1..k : NodeLog(i)[m].term = NodeLog(j)[m].term

\* §5.4.3  Committed entries at the same index have the same term.
StateMachineSafetyInv ==
    \A i, j \in Server :
        LET minC == Min({NodeCommitIndex(i), NodeCommitIndex(j)})
        IN \A k \in 1..minC :
            /\ k <= Len(NodeLog(i))
            /\ k <= Len(NodeLog(j))
            => NodeLog(i)[k].term = NodeLog(j)[k].term

\* §5.3  A leader's log only grows while it remains leader.
LeaderAppendOnlyInv ==
    l = 1 \/
    LET prev == TraceLog[l - 1]
    IN \A i \in Server :
        LET pRole == prev.state[ToString(i)].state
            pLog  == prev.state[ToString(i)].log
        IN pRole = "Leader" /\ NodeRole(i) = "Leader"
           => /\ Len(NodeLog(i)) >= Len(pLog)
              /\ \A k \in 1..Len(pLog) :
                    NodeLog(i)[k].term = pLog[k].term

\* §5.1  A server's term never decreases.
TermMonotonicityInv ==
    l = 1 \/
    LET prev == TraceLog[l - 1]
    IN \A i \in Server :
        NodeTerm(i) >= prev.state[ToString(i)].currentTerm

\* raft-rs enforces strict commit monotonicity (raft_log.rs commit_to).
\* The TLA+ spec raft.tla allows commitIndex to decrease; raft-rs does not.
CommitMonotonicityInv ==
    l = 1 \/
    LET prev == TraceLog[l - 1]
    IN \A i \in Server :
        NodeCommitIndex(i) >= prev.state[ToString(i)].commitIndex

\* commitIndex never exceeds log length.
CommittedEntriesInLogInv ==
    \A i \in Server :
        NodeCommitIndex(i) <= Len(NodeLog(i))

\* applied never exceeds persisted.
PersistedAppliedOrderingInv ==
    \A i \in Server :
        NodeState(i).applied <= NodeState(i).persisted

\* -------------------------------------------------------------------------
\* Alias for TLC counterexample output
\* -------------------------------------------------------------------------

TraceAlias ==
    [
        l |-> l,
        action  |-> IF l <= Len(TraceLog) THEN logline.action ELSE "END",
        node    |-> IF l <= Len(TraceLog) THEN logline.node   ELSE 0,
        states  |-> IF l <= Len(TraceLog) THEN
            [i \in Server |-> [
                term       |-> NodeTerm(i),
                role       |-> NodeRole(i),
                logLen     |-> Len(NodeLog(i)),
                commitIdx  |-> NodeCommitIndex(i)
            ]]
            ELSE "END"
    ]

===============================================================================
