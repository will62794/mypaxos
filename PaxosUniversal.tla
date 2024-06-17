-------------------------------- MODULE PaxosUniversal -------------------------------

\*
\* A specification of Paxos in a so-called "universal" message passing style. 
\* 
\* We get rid of all notions of separate roles (proposers/acceptors/learners) and
\* simply model the protocol based on the local state of N processes that need
\* to achieve consensus on a value. We also get rid of any protocol specific
\* message passing details by having each node broadcast their entire state into
\* the network on every state update.
\*
EXTENDS Integers, FiniteSets, TLC

\* Remove distinctions between proposer/Node concept i.e., collapse them into one.
CONSTANT Node
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

CONSTANT None

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Node
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
  
\*   
\* A global table mapping from ballot numbers to values for that ballot.
\* Initialized once, non-deterministically, in the initial state. 
\* 
\* We can view this as a prophecy variable that resolves the non-determinism in
\* value choice by each node initially, while also ensuring value uniqueness per
\* ballot.
\* 
VARIABLE proposals 

\* The set of all messages that have been sent.
VARIABLE msgs

\************************************ 
\* Node-local state variables.
\************************************

\* The largest ballot number seen by a node.
VARIABLE maxBal

\* <<maxVBal[a], maxVal[a]>> is the vote with the largest
\* ballot number cast by a; it equals <<-1, None>> if
\* a has not cast any vote.
VARIABLE maxVal 
VARIABLE maxVBal 

\* The value chosen/decided at each node.
VARIABLE chosen   

(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)

vars == <<maxBal, maxVBal, maxVal, chosen, msgs, proposals>>

TypeOK == /\ maxBal \in [Node -> Ballot \cup {-1}]
          /\ maxVBal \in [Node -> Ballot \cup {-1}]
          /\ maxVal \in [Node -> Value \cup {None}]
          /\ msgs \subseteq [
                    from : Node,
                    maxBal : Ballot \cup {-1},
                    maxVBal : Ballot \cup {-1},
                    maxVal : Value \cup {None}
            ]
          /\ chosen \in [Node -> Value \cup {None}]
          /\ proposals \in [Ballot -> Value \cup {None}]

\* We can view a message "broadcast" as simply recording of a process state at
\* some point in its history. Thus, this allows other nodes to "read" the state
\* of this process at some point in its history (e.g. some past state).
BroadcastPostState(sender) == msgs' = msgs \cup {[
    from |-> sender,
    maxBal |-> maxBal'[sender],
    maxVBal |-> maxVBal'[sender],
    maxVal |-> maxVal'[sender]
]}

Init == 
    /\ maxBal = [a \in Node |-> -1]
    /\ maxVBal = [a \in Node |-> -1]
    /\ maxVal = [a \in Node |-> None]
    /\ chosen = [n \in Node |-> None]
    /\ msgs = {}
    \* We assume in this model that values for a given proposal/ballot number
    \* are assigned in some way that is unique to each proposal/ballot, but we
    \* don't care how they are assigned. In practice, this might be done by
    \* assigning proposal numbers uniquely to each distinct node, so that when
    \* they pick a value for a ballot, they can be sure it doesn't conflict with
    \* any already chosen value for that ballot.
    /\ proposals \in [Ballot -> Value]

\* In classic Paxos, "1a" messages are typically sent by proposers at will,
\* without any preconditions, so we can view this as essentially equivalent to
\* acceptors being able to "magically" execute a 1b/prepare action for a given
\* ballot number, which is how we model things here.
\* 
\* We refer to this action as a node "preparing" in some new ballot number b.
\* 
Prepare(n, b) == 
    /\ b > maxBal[n]
    /\ maxBal' = [maxBal EXCEPT ![n] = b]
    /\ UNCHANGED <<maxVBal, maxVal, chosen, proposals>>
    /\ BroadcastPostState(n)

\* 
\* In '2a', a node checks that a quorum is prepared at ballot 'b', and checks
\* whether any values were chosen by nodes in this quorum at earlier ballots. If
\* so, it can go ahead and accept a value with the highest such ballot.
\* 
\* Otherwise, it is free to pick a value, in accordance with the proposal
\* uniqueness enforced by the global proposal table, which gives a static
\* assignment of values to ballots.
\* 

Q1b(Q, b) == {m \in msgs : m.from \in Q /\ m.maxBal = b}
Q1bv(Q, b) == {m \in Q1b(Q,b) : m.maxVBal \geq 0}

\* Nobody in quorum has previously accepted a value.
\* 
\* Can we view 2a as simply a "distributed read" type action, where the
\* information about this read can then be sent around to others allowing
\* them to accept a certain proposal if they are able to?
\* 
\* Sometimes messages only carry information that doesn't need to be written down locally, but represent the 
\* result of a "distributed read" by a node?
\* 
Phase2aFree(n, b, v, Q) ==
  /\ \A a \in Q : \E m \in Q1b(Q,b) : m.from = a
  /\ Q1bv(Q,b) = {} \* No proposals have been accepted in earlier ballots.
  \* Ensure proposal uniqueness via global static assignment.
  /\ proposals[b] = v
  /\ b > maxBal[n]
  /\ maxBal' = [maxBal EXCEPT ![n] = b] 
  /\ maxVBal' = [maxVBal EXCEPT ![n] = b] 
  /\ maxVal' = [maxVal EXCEPT ![n] = v]
  /\ UNCHANGED <<chosen, proposals>>
  /\ BroadcastPostState(n)

\* Some nodes in quorum have previously accepted a value.
Phase2aBound(n, b, v, Q) ==
  /\ \A a \in Q : \E m \in Q1b(Q,b) : m.from = a
  /\ \E m \in Q1bv(Q, b) : 
        /\ m.maxVal = v
        \* v is the value accepted in Q with the highest ballot number.
        /\ \A mm \in Q1bv(Q, b) : m.maxVBal \geq mm.maxVBal 
  /\ b >= maxBal[n]
  /\ maxBal' = [maxBal EXCEPT ![n] = b] 
  /\ maxVBal' = [maxVBal EXCEPT ![n] = b] 
  /\ maxVal' = [maxVal EXCEPT ![n] = v]
  /\ UNCHANGED <<chosen, proposals>>
  /\ BroadcastPostState(n)

Phase2b(n, b) == 
    \* A node directly checks if it can accept a value by seeing if some other value has accepted it at
    \* a ballot that is not older than its latest ballot. If so, it can go ahead and accept it itself.
    \E m \in msgs : 
        /\ m.maxVBal = b
        /\ m.maxVBal \geq maxBal[n]
        /\ m.maxVBal >= 0
        /\ maxBal' = [maxBal EXCEPT ![n] = m.maxVBal] 
        /\ maxVBal' = [maxVBal EXCEPT ![n] = m.maxVBal] 
        /\ maxVal' = [maxVal EXCEPT ![n] = m.maxVal]
        /\ BroadcastPostState(n)
        /\ UNCHANGED <<chosen, proposals>>
     
\* A node locally learns/decides a value by seeing if a quorum have accepted
\* it at a given ballot number.
\* Note that this action only updates node-local state (`chosen`), so we don't explicitly 
\* execute a state broadcast here.
Learn(n, b, v, Q) ==
    /\ \A a \in Q : \E m \in msgs : 
        /\ m.from = a 
        /\ m.maxVBal = b 
        /\ m.maxVal = v
    /\ chosen' = [chosen EXCEPT ![n] = v]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposals>>

\* The next-state relation. 
Next == 
    \/ \E b \in Ballot, n \in Node : Prepare(n, b)
    \/ \E b \in Ballot, v \in Value, n \in Node, Q \in Quorum : Phase2aFree(n, b, v, Q)
    \/ \E b \in Ballot, v \in Value, n \in Node, Q \in Quorum : Phase2aBound(n, b, v, Q)
    \/ \E n \in Node, b \in Ballot : Phase2b(n, b)
    \/ \E n \in Node : \E b \in Ballot, v \in Value, Q \in Quorum : Learn(n, b, v, Q)

Spec == Init /\ [][Next]_vars

\* Core safety property: if two nodes have chosen values, they must be the same.
Safety == 
    \A ni,nj \in Node : 
        (chosen[ni] # None /\ chosen[nj] # None) => chosen[ni] = chosen[nj]

----------------------------------------------------------------------------

\* 
\* Auxiliary properties.
\* 

\* Inv == Cardinality(chosen) <= 1 
Inv == Cardinality(msgs) <= 2

Symmetry == Permutations(Node) \cup Permutations(Value)

Cover1 == \A n \in Node : chosen[n] = None
Cover2 == ~(\A n \in Node : chosen[n] # None)

============================================================================
