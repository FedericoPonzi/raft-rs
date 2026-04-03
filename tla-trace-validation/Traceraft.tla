------------------------------- MODULE Traceraft -------------------------------
\* Trace validation for raft-rs.
\*
\* EXTENDS raft.tla and uses its actions. For receive actions, the trace
\* tells us the exact message. We construct the spec message from trace
\* fields, inject it into the bag if missing, then call the spec handler.
\*
\* The injection is done by redefining Send/Discard/Reply to operate on
\* a bag that includes the injected message.

EXTENDS raft, Json, IOUtils, Sequences

ASSUME TLCGet("config").mode = "bfs"
ASSUME TLCGet("config").worker = 1

JsonFile ==
    IF "RAFT_TRACE" \in DOMAIN IOEnv THEN IOEnv.RAFT_TRACE
    ELSE "traces/rand3n_0.ndjson"

JsonLog == ndJsonDeserialize(JsonFile)
TraceLog == SelectSeq(JsonLog, LAMBDA entry: entry.tag = "raft_trace")
ASSUME TLCEval(Print(<<"Trace:", JsonFile, "Length:", Len(TraceLog)>>, TRUE))

TraceValues ==
    {TraceLog[i].value : i \in {j \in DOMAIN TraceLog : "value" \in DOMAIN TraceLog[j]}}

VARIABLE l
logline == TraceLog[l]
PostState == IF l < Len(TraceLog)
             THEN TraceLog[l+1].state[ToString(logline.node)]
             ELSE logline.state[ToString(logline.node)]

TraceInit ==
    /\ l = 2
    /\ Init
    /\ TraceLog[1].action = "Init"

\* =========================================================================
\* Inject a message into the bag, then call Discard or Reply.
\* This ensures the handler finds its expected message.
\* =========================================================================

InjectAndDiscard(m) ==
    messages' = WithoutMessage(m, WithMessage(m, messages))

InjectAndReply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, WithMessage(request, messages)))

\* =========================================================================
\* Composed actions
\* =========================================================================

TimeoutWithSelfVote(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state'          = [state EXCEPT ![i] = Candidate]
    /\ votedFor'       = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = (i :> log[i])]
    /\ UNCHANGED <<messages, log, commitIndex, nextIndex, matchIndex, elections>>

BecomeLeaderWithNoop(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ LET newLog == Append(log[i], [term |-> currentTerm[i], value |-> "noop"])
       IN /\ state' = [state EXCEPT ![i] = Leader]
          /\ nextIndex' = [nextIndex EXCEPT ![i] = [k \in Server |-> Len(log[i]) + 1]]
          /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Server |->
                               IF k = i THEN Len(newLog) ELSE 0]]
          /\ elections' = elections \cup
                              {[eterm |-> currentTerm[i], eleader |-> i, elog |-> log[i],
                                evotes |-> votesGranted[i], evoterLog |-> voterLog[i]]}
          /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, commitIndex>>

\* =========================================================================
\* Trace actions
\* =========================================================================

IsTimeout ==
    /\ logline.action = "Timeout"
    /\ LET i == logline.node
       IN IF PostState.state = "Candidate"
          THEN TimeoutWithSelfVote(i)
          ELSE UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars>>

IsRequestVote ==
    /\ logline.action = "RequestVote"
    /\ RequestVote(logline.node, logline.target)

IsBecomeLeader ==
    /\ logline.action = "BecomeLeader"
    /\ IF state[logline.node] = Candidate
       THEN BecomeLeaderWithNoop(logline.node)
       ELSE UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars>>

IsClientRequest ==
    /\ logline.action = "ClientRequest"
    /\ ClientRequest(logline.node, logline.value)

IsAdvanceCommitIndex ==
    /\ logline.action = "AdvanceCommitIndex"
    /\ AdvanceCommitIndex(logline.node)

IsAppendEntries ==
    /\ logline.action = "AppendEntries"
    /\ AppendEntries(logline.node, logline.target)

IsHandleRequestVoteRequest ==
    /\ logline.action = "HandleRequestVoteRequest"
    /\ LET i == logline.node
           j == logline.target
           tm == logline.message
           m == [mtype |-> RequestVoteRequest, mterm |-> tm.mterm,
                 mlastLogTerm |-> tm.mlastLogTerm, mlastLogIndex |-> tm.mlastLogIndex,
                 msource |-> j, mdest |-> i]
           logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                    \/ /\ m.mlastLogTerm = LastTerm(log[i])
                       /\ m.mlastLogIndex >= Len(log[i])
           grant == /\ m.mterm = currentTerm[i] /\ logOk /\ votedFor[i] \in {Nil, j}
       IN /\ m.mterm <= currentTerm[i]
          /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
             \/ ~grant /\ UNCHANGED votedFor
          /\ InjectAndReply(
                 [mtype |-> RequestVoteResponse, mterm |-> currentTerm[i],
                  mvoteGranted |-> grant, mlog |-> log[i],
                  msource |-> i, mdest |-> j],
                 m)
          /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

IsHandleRequestVoteResponse ==
    /\ logline.action = "HandleRequestVoteResponse"
    /\ LET i == logline.node
           j == logline.target
           tm == logline.message
           m == [mtype |-> RequestVoteResponse, mterm |-> tm.mterm,
                 mvoteGranted |-> tm.mvoteGranted, mlog |-> log[j],
                 msource |-> j, mdest |-> i]
       IN LET wouldBecomeLeader ==
                /\ state[i] = Candidate
                /\ tm.mvoteGranted
                /\ m.mterm = currentTerm[i]
                /\ (votesGranted[i] \cup {j}) \in Quorum
          IN IF wouldBecomeLeader
          THEN \* HandleRVRAndBecomeLeader
               /\ m.mterm = currentTerm[i]
               /\ m.mvoteGranted
               /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
               /\ LET newGranted == votesGranted[i] \cup {j}
                  IN /\ votesGranted' = [votesGranted EXCEPT ![i] = newGranted]
                     /\ newGranted \in Quorum
               /\ voterLog' = [voterLog EXCEPT ![i] = voterLog[i] @@ (j :> m.mlog)]
               /\ LET newLog == Append(log[i], [term |-> currentTerm[i], value |-> "noop"])
                  IN /\ state' = [state EXCEPT ![i] = Leader]
                     /\ nextIndex' = [nextIndex EXCEPT ![i] = [k \in Server |-> Len(log[i]) + 1]]
                     /\ matchIndex' = [matchIndex EXCEPT ![i] = [k \in Server |->
                                          IF k = i THEN Len(newLog) ELSE 0]]
                     /\ log' = [log EXCEPT ![i] = newLog]
                     /\ elections' = elections \cup
                                         {[eterm |-> currentTerm[i], eleader |-> i, elog |-> log[i],
                                           evotes |-> votesGranted[i] \cup {j},
                                           evoterLog |-> voterLog[i] @@ (j :> m.mlog)]}
               /\ InjectAndDiscard(m)
               /\ UNCHANGED <<currentTerm, votedFor, commitIndex>>
          ELSE IF m.mterm < currentTerm[i]
               THEN /\ InjectAndDiscard(m)
                    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>
               ELSE /\ m.mterm = currentTerm[i]
                    /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
                    /\ \/ /\ m.mvoteGranted
                          /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                          /\ voterLog' = [voterLog EXCEPT ![i] = voterLog[i] @@ (j :> m.mlog)]
                       \/ /\ ~m.mvoteGranted /\ UNCHANGED <<votesGranted, voterLog>>
                    /\ InjectAndDiscard(m)
                    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars>>

IsHandleAppendEntriesRequest ==
    /\ logline.action = "HandleAppendEntriesRequest"
    /\ LET i == logline.node
           j == logline.target
           tm == logline.message
           entry == IF Len(tm.mentries) > 0
                    THEN <<[term |-> tm.mentries[1].term, value |-> tm.mentries[1].value]>>
                    ELSE << >>
           m == [mtype |-> AppendEntriesRequest, mterm |-> tm.mterm,
                 mprevLogIndex |-> tm.mprevLogIndex,
                 mprevLogTerm |-> tm.mprevLogTerm,
                 mentries |-> entry, mlog |-> log[j],
                 mcommitIndex |-> tm.mcommitIndex,
                 msource |-> j, mdest |-> i]
           logOk == \/ m.mprevLogIndex = 0
                    \/ /\ m.mprevLogIndex > 0
                       /\ m.mprevLogIndex <= Len(log[i])
                       /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
           index == m.mprevLogIndex + 1
       IN IF /\ m.mentries /= << >>
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
          THEN \* Atomic: append/truncate + reply
               /\ \/ /\ Len(log[i]) >= index /\ log[i][index].term /= m.mentries[1].term
                     /\ log' = [log EXCEPT ![i] =
                         Append(SubSeq(log[i], 1, m.mprevLogIndex), m.mentries[1])]
                  \/ /\ Len(log[i]) = m.mprevLogIndex
                     /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                  \/ /\ Len(log[i]) >= index /\ log[i][index].term = m.mentries[1].term
                     /\ UNCHANGED log
               /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.mcommitIndex, m.mprevLogIndex + Len(m.mentries)})]
               /\ InjectAndReply(
                      [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i],
                       msuccess |-> TRUE,
                       mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                       msource |-> i, mdest |-> j], m)
               /\ UNCHANGED <<serverVars, candidateVars, leaderVars>>
          ELSE \* Use standard handler (reject, heartbeat, candidate->follower)
               /\ m.mterm <= currentTerm[i]
               /\ \/ \* reject
                     /\ \/ m.mterm < currentTerm[i]
                        \/ /\ m.mterm = currentTerm[i] /\ state[i] = Follower /\ ~logOk
                     /\ InjectAndReply(
                            [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i],
                             msuccess |-> FALSE, mmatchIndex |-> 0,
                             msource |-> i, mdest |-> j], m)
                     /\ UNCHANGED <<serverVars, logVars>>
                  \/ \* candidate -> follower
                     /\ m.mterm = currentTerm[i] /\ state[i] = Candidate
                     /\ state' = [state EXCEPT ![i] = Follower]
                     /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
                  \/ \* accept heartbeat (already done)
                     /\ m.mterm = currentTerm[i] /\ state[i] = Follower /\ logOk
                     /\ m.mentries = << >>
                     /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.mcommitIndex, Len(log[i])})]
                     /\ InjectAndReply(
                            [mtype |-> AppendEntriesResponse, mterm |-> currentTerm[i],
                             msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex,
                             msource |-> i, mdest |-> j], m)
                     /\ UNCHANGED <<serverVars, log>>
               /\ UNCHANGED <<candidateVars, leaderVars>>

IsHandleAppendEntriesResponse ==
    /\ logline.action = "HandleAppendEntriesResponse"
    /\ LET i == logline.node
           j == logline.target
           tm == logline.message
           m == [mtype |-> AppendEntriesResponse, mterm |-> tm.mterm,
                 msuccess |-> tm.msuccess, mmatchIndex |-> tm.mmatchIndex,
                 msource |-> j, mdest |-> i]
       IN IF m.mterm = currentTerm[i]
          THEN /\ \/ /\ m.msuccess
                     /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                     /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                  \/ /\ ~m.msuccess
                     /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                     /\ UNCHANGED matchIndex
               /\ InjectAndDiscard(m)
               /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>
          ELSE /\ InjectAndDiscard(m)
               /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

IsUpdateTerm ==
    /\ logline.action = "UpdateTerm"
    /\ LET tm == logline.message
       IN /\ tm.mterm > currentTerm[logline.node]
          /\ currentTerm' = [currentTerm EXCEPT ![logline.node] = tm.mterm]
          /\ state'       = [state       EXCEPT ![logline.node] = Follower]
          /\ votedFor'    = [votedFor    EXCEPT ![logline.node] = Nil]
          /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

IsDropMessage ==
    /\ logline.action = "DropMessage"
    /\ LET n == logline.node
       IN messages' = [m \in {m \in DOMAIN messages :
                                 m.mdest /= n /\ m.msource /= n}
                       |-> messages[m]]
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

IsRecoverNetwork ==
    /\ logline.action = "RecoverNetwork"
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars>>

\* =========================================================================
\* TraceNext
\* =========================================================================

TraceNext ==
    /\ l < Len(TraceLog)
    /\ l' = l + 1
    /\ \/ IsTimeout      \/ IsRequestVote
       \/ IsBecomeLeader \/ IsClientRequest
       \/ IsAdvanceCommitIndex \/ IsAppendEntries
       \/ IsHandleRequestVoteRequest \/ IsHandleRequestVoteResponse
       \/ IsHandleAppendEntriesRequest \/ IsHandleAppendEntriesResponse
       \/ IsUpdateTerm \/ IsDropMessage \/ IsRecoverNetwork
    /\ allLogs' = allLogs \cup {log[i] : i \in Server}

TraceSpec == TraceInit /\ [][TraceNext]_<<l, vars>>

\* =========================================================================
\* Safety invariants
\* =========================================================================

ElectionSafetyInv ==
    \A i, j \in Server :
        /\ i /= j /\ state[i] = Leader /\ state[j] = Leader
        => currentTerm[i] /= currentTerm[j]

LogMatchingInv ==
    \A i, j \in Server :
        \A k \in 1..Min({Len(log[i]), Len(log[j])}) :
            log[i][k].term = log[j][k].term
            => \A n \in 1..k : log[i][n].term = log[j][n].term

StateMachineSafetyInv ==
    \A i, j \in Server :
        LET minC == Min({commitIndex[i], commitIndex[j]})
        IN \A k \in 1..minC :
            /\ k <= Len(log[i]) /\ k <= Len(log[j])
            => log[i][k].term = log[j][k].term

CommitIdxLELogLenInv ==
    \A i \in Server : commitIndex[i] <= Len(log[i])

\* =========================================================================
\* View, termination, matching
\* =========================================================================

TraceView == <<vars, l>>
Termination == l = Len(TraceLog) => TLCSet("exit", TRUE)

TraceMatched ==
    [](l <= Len(TraceLog) =>
       [](TLCGet("queue") \in Nat \ {0} \/ l >= Len(TraceLog)))

TraceMatchedNonTrivially == TLCGet("stats").diameter >= 2

TraceAlias ==
    [ l |-> l,
      _action |-> IF l <= Len(TraceLog) THEN logline.action ELSE "END",
      _node   |-> IF l <= Len(TraceLog) THEN logline.node ELSE 0,
      currentTerm |-> currentTerm, state |-> state,
      log_lens |-> [i \in Server |-> Len(log[i])],
      commitIndex |-> commitIndex, votesGranted |-> votesGranted,
      msg_count |-> Cardinality(DOMAIN messages) ]

===============================================================================
