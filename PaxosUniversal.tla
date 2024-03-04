-------------------------------- MODULE PaxosUniversal -------------------------------

\*
\* This is a spec of Paxos in what we are referring to as a "universal" message
\* passing style. 
\* 
\* We eschew all notions of separate roles (proposers/acceptors/learners) and
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
  
\* The largest ballot number seen by a node.
VARIABLE maxBal

\* <<maxVBal[a], maxVal[a]>> is the vote with the largest
\* ballot number cast by a; it equals <<-1, None>> if
\* a has not cast any vote.
VARIABLE maxVal 
VARIABLE maxVBal 

\* The value chosen/decided at each node.
VARIABLE chosen   

\* The set of all messages that have been sent.
VARIABLE msgs

\* A global table mapping from ballot numbers to values for that ballot.
\* Initialized once, non-deterministically, in the initial state.
VARIABLE proposals 

vars == <<maxBal, maxVBal, maxVal, chosen, msgs, proposals>>
  
(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
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
BroadcastPost(sender) == msgs' = msgs \cup {[
    from |-> sender,
    maxBal |-> maxBal'[sender],
    maxVBal |-> maxVBal'[sender],
    maxVal |-> maxVal'[sender]
]}

\* Establish some fixed, arbitrary ordering on nodes.
\* Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y
\* NodeOrder == CHOOSE f \in [Node -> 0..Cardinality(Node)] : Injective(f)

Init == /\ maxBal = [a \in Node |-> -1]
        /\ maxVBal = [a \in Node |-> -1]
        /\ maxVal = [a \in Node |-> None]
        /\ chosen = [n \in Node |-> None]
        /\ msgs = {}
        \* Stores some arbitrary global table mapping from ballot numbers
        \* to the value for that ballot. We assume in this model that values
        \* for a given proposal/ballot number are assigned in some way that is unique
        \* to each proposal/ballot, but we don't care how they are assigned. For example,
        \* in practice, this might be done by assigning proposal numbers uniquely to each 
        \* distinct node, so that when they pick a value for a ballot, they can be sure 
        \* it doesn't conflict with any already chosen value for that ballot.
        /\ proposals \in [Ballot -> Value]

\* 1a messages are typically sent by proposers at will, without any
\* preconditions, so we can view this as essentially equivalent to acceptors
\* being able to "magically" execute a 1b action for a given ballot number. This
\* is how we model things here.
Prepare(b, n) == 
    /\ b >= maxBal[n]
    /\ maxBal' = [maxBal EXCEPT ![n] = b]
    /\ UNCHANGED <<maxVBal, maxVal, chosen, proposals>>
    /\ BroadcastPost(n)

Q1b(Q, b) == {m \in msgs : m.from \in Q /\ m.maxBal = b}
Q1bv(Q, b) == {m \in Q1b(Q,b) : m.maxVBal \geq 0}

\* Why does proposer need to designated aggregator/checker of the phase 2a
\* condition? Couldn't any node/acceptor just do it? If we do a broadcast, this
\* seems natural, but I guess it is not necessarily natural if you assume a
\* point to point broadcast model, since 1b messages are sent directly to some
\* proposer.
Phase2a(b, v, n, Q) ==
  /\ \A a \in Q : \E m \in Q1b(Q,b) : m.from = a  \* is this really necessary? can't anyone gather this info?
  /\ \/ Q1bv(Q,b) = {}
     \/ \E m \in Q1bv(Q, b) : 
        /\ m.maxVal = v
        /\ \A mm \in Q1bv(Q, b) : m.maxVBal \geq mm.maxVBal 
  \* Shouldn't an acceptor be able to go ahead and accept a new value at this point
  \* if allowed?
  \* Problem seems to be that we still need to deal with proposal number uniqueness, though (?)
  /\ proposals[b] = v
  /\ (maxVBal[n] = b) => maxVal[n] = None \* Cannot have already picked a value for this ballot. 
  /\ b >= maxBal[n]
  /\ maxBal' = [maxBal EXCEPT ![n] = b] 
  /\ maxVBal' = [maxVBal EXCEPT ![n] = b] 
  /\ maxVal' = [maxVal EXCEPT ![n] = v]
  /\ UNCHANGED <<chosen, proposals>>
  /\ BroadcastPost(n)

Phase2b(n) == 
    \* A node directly checks if it can accept a value by seeing if some other value has accepted it at
    \* a ballot that is not older than its latest ballot. If so, it can go ahead and accept it itself.
    \E m \in msgs : 
        /\ m.maxVBal \geq maxBal[n]
        /\ m.maxVBal >= 0
        /\ maxBal' = [maxBal EXCEPT ![n] = m.maxVBal] 
        /\ maxVBal' = [maxVBal EXCEPT ![n] = m.maxVBal] 
        /\ maxVal' = [maxVal EXCEPT ![n] = m.maxVal]
        /\ BroadcastPost(n)
        /\ UNCHANGED <<chosen, proposals>>
     
\* A node locally learns/decides a value by seeing if a quorum have accepted
\* it at a given ballot number.
\* Note that this action only updates node-local state (`chosen`), so we don't explicitly 
\* execute a state broadcast here.
Learn(n, b, v, Q) ==
    /\ \A a \in Q : maxVBal[a] = b /\ maxVal[a] = v
    /\ chosen' = [chosen EXCEPT ![n] = v]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs, proposals>>

\* The next-state relation. 
Next == 
    \/ \E b \in Ballot, n \in Node : Prepare(b, n)
    \/ \E b \in Ballot, v \in Value, n \in Node, Q \in Quorum : Phase2a(b, v, n, Q)
    \/ \E a \in Node : \E p \in Node : Phase2b(a)
    \/ \E a \in Node : \E b \in Ballot, v \in Value, Q \in Quorum : Learn(a, b, v, Q)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------

\* If two nodes have chosen values, they must be the same.
Safety == \A n,n2 \in Node : 
            (chosen[n] # None /\ chosen[n2] # None) => chosen[n] = chosen[n2]

\* Inv == Cardinality(chosen) <= 1 
Inv == Cardinality(msgs) <= 2

Symmetry == Permutations(Node)

Cover1 == \A n \in Node : chosen[n] = None
Cover2 == ~(\A n \in Node : chosen[n] # None)

============================================================================
