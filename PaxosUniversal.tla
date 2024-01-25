-------------------------------- MODULE PaxosUniversal -------------------------------
(***************************************************************************)
(* This is a specification of the Paxos algorithm without explicit leaders *)
(* or learners.  It refines the spec in Voting                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC
-----------------------------------------------------------------------------
(***************************************************************************)
(* The constant parameters and the set Ballots are the same as in Voting.  *)
(***************************************************************************)
\* Get rid of all separation between proposer/Node concept i.e., collapse them
\* into one.
CONSTANT Value, Node, Quorum
CONSTANT None
CONSTANT Ballot

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Node
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
      
  (*************************************************************************)
  (* An unspecified value that is not a ballot number.                     *)
  (*************************************************************************)
  
(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages.  The messages are explained below     *)
(* with the actions that send them.                                        *)
(***************************************************************************)
\* Message ==      [type : {"1a"}, bal : Ballot]
        \*    \cup [type : {"1b"}, acc : Node, bal : Ballot, 
                \*  mbal : Ballot \cup {-1}, mval : Value \cup {None}]
        \*    \cup [type : {"2a"}, bal : Ballot, val : Value]
        \*    \cup [type : {"2b"}, acc : Node, bal : Ballot, val : Value]
-----------------------------------------------------------------------------
VARIABLE maxBal, 
         maxVBal, \* <<maxVBal[a], maxVal[a]>> is the vote with the largest
         maxVal,    \* ballot number cast by a; it equals <<-1, None>> if
                    \* a has not cast any vote.
         chosen,    \* chosen value at each node.
         msgs     \* The set of all messages that have been sent.

(***************************************************************************)
(* NOTE:                                                                   *)
(* The algorithm is easier to understand in terms of the set msgs of all   *)
(* messages that have ever been sent.  A more accurate model would use     *)
(* one or more variables to represent the messages actually in transit,    *)
(* and it would include actions representing message loss and duplication  *)
(* as well as message receipt.                                             *)
(*                                                                         *)
(* In the current spec, there is no need to model message loss because we  *)
(* are mainly concerned with the algorithm's safety property.  The safety  *)
(* part of the spec says only what messages may be received and does not   *)
(* assert that any message actually is received.  Thus, there is no        *)
(* difference between a lost message and one that is never received.  The  *)
(* liveness property of the spec that we check makes it clear what what    *)
(* messages must be received (and hence either not lost or successfully    *)
(* retransmitted if lost) to guarantee progress.                           *)
(***************************************************************************)

vars == <<maxBal, maxVBal, maxVal, chosen, msgs>>
  (*************************************************************************)
  (* It is convenient to define some identifier to be the tuple of all     *)
  (* variables.  I like to use the identifier `vars'.                      *)
  (*************************************************************************)
  
(***************************************************************************)
(* The type invariant and initial predicate.                               *)
(***************************************************************************)
TypeOK == /\ maxBal \in [Node -> Ballot \cup {-1}]
          /\ maxVBal \in [Node -> Ballot \cup {-1}]
          /\ maxVal \in [Node -> Value \cup {None}]
        \*   /\ msgs \subseteq Message
          

Init == /\ maxBal = [a \in Node |-> -1]
        /\ maxVBal = [a \in Node |-> -1]
        /\ maxVal = [a \in Node |-> None]
        /\ chosen = [n \in Node |-> None]
        /\ msgs = {}

(***************************************************************************)
(* The actions.  We begin with the subaction (an action that will be used  *)
(* to define the actions that make up the next-state action.               *)
(***************************************************************************)
Send(m) == msgs' = msgs \cup {m}

BroadcastPost(sender) == msgs' = msgs \cup {[
    from |-> sender,
    maxBal |-> maxBal'[sender],
    maxVBal |-> maxVBal'[sender],
    maxVal |-> maxVal'[sender]
]}


\* Allow any node to initiate a proposal to try to get it accepted.
Phase1a(b, n) == 
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, chosen>>
    /\ BroadcastPost(n)
 
(***************************************************************************)
(* Upon receipt of a ballot b phase 1a message, Node a can perform a   *)
(* Phase1b(a) action only if b > maxBal[a].  The action sets maxBal[a] to  *)
(* b and sends a phase 1b message to the leader containing the values of   *)
(* maxVBal[a] and maxVal[a].                                               *)
(***************************************************************************)
Phase1b(n) == 
    \E m \in msgs :
        \* /\ m.proposer = p
        \* /\ m.type = "1a"
        /\ m.maxBal > maxBal[n]
        /\ maxBal' = [maxBal EXCEPT ![n] = m.maxBal]
        \* /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal, 
                \* mbal |-> maxVBal[a], mval |-> maxVal[a], proposer |-> p])
        /\ UNCHANGED <<maxVBal, maxVal, chosen>>
        /\ BroadcastPost(n)


(***************************************************************************)
(* The Phase2a(b, v) action can be performed by the ballot b leader if two *)
(* conditions are satisfied: (i) it has not already performed a phase 2a   *)
(* action for ballot b and (ii) it has received ballot b phase 1b messages *)
(* from some quorum Q from which it can deduce that the value v is safe at *)
(* ballot b.  These enabling conditions are the first two conjuncts in the *)
(* definition of Phase2a(b, v).  This second conjunct, expressing          *)
(* condition (ii), is the heart of the algorithm.  To understand it,       *)
(* observe that the existence of a phase 1b message m in msgs implies that *)
(* m.mbal is the highest ballot number less than m.bal in which Node   *)
(* m.acc has or ever will cast a vote, and that m.mval is the value it     *)
(* voted for in that ballot if m.mbal # -1.  It is not hard to deduce from *)
(* this that the second conjunct implies that there exists a quorum Q such *)
(* that ShowsSafeAt(Q, b, v) (where ShowsSafeAt is defined in module       *)
(* Voting).                                                                *)
(*                                                                         *)
(* The action sends a phase 2a message that tells any Node a that it   *)
(* can vote for v in ballot b, unless it has already set maxBal[a]         *)
(* greater than b (thereby promising not to vote in ballot b).             *)
(***************************************************************************)
Phase2a(b, v, n) ==
\*   /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.proposer = n
  /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : \*/\ m.type = "1b"
                                 /\ m.from \in Q
                                 /\ m.maxBal = b}
            Q1bv == {m \in Q1b : m.maxBal \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m.from = a 
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv : 
                    /\ m.maxVal = v
                    /\ \A mm \in Q1bv : m.maxVBal \geq mm.maxVBal 
\*   /\ Send([type |-> "2a", bal |-> b, val |-> v, proposer |-> n]) 
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, chosen>>
  /\ BroadcastPost(n)

(***************************************************************************)
(* The Phase2b(a) action is performed by Node a upon receipt of a      *)
(* phase 2a message.  Node a can perform this action only if the       *)
(* message is for a ballot number greater than or equal to maxBal[a].  In  *)
(* that case, the Node votes as directed by the phase 2a message,      *)
(* setting maxBVal[a] and maxVal[a] to record that vote and sending a      *)
(* phase 2b message announcing its vote.  It also sets maxBal[a] to the    *)
(* message's.  ballot number                                               *)
(***************************************************************************)
Phase2b(n) == 
    \* Why not just directly tally quorum needed to go ahead and complete 2b?
    \* Proposers typically play a kind of "information aggregator" role in standard Paxos model (?)
    \E m \in msgs : 
        \* /\ m.type = "2a"
        /\ m.maxBal \geq maxBal[n]
        \* /\ maxBal' = [maxBal EXCEPT ![n] = m.bal] 
        \* /\ maxVBal' = [maxVBal EXCEPT ![n] = m.bal] 
        \* /\ maxVal' = [maxVal EXCEPT ![n] = m.val]
        \* /\ Send([type |-> "2b", acc |-> a,
                \* bal |-> m.bal, val |-> m.val, proposer |-> None])
        /\ BroadcastPost(n)
     

(***************************************************************************)
(* In an implementation, there will be learner processes that learn from   *)
(* the phase 2b messages if a value has been chosen.  The learners are     *)
(* omitted from this abstract specification of the algorithm.              *)
(***************************************************************************)
                                                  


(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Next == 
    \/ \E b \in Ballot : \E n \in Node : Phase1a(b, n)
    \/ \E n \in Node : Phase1b(n)
    \/ \E b \in Ballot : \E v \in Value : \E n \in Node : Phase2a(b, v, n)
    \* \/ \E a \in Node : \E p \in Node : Phase2b(a)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
(***************************************************************************)
(* As we observed, votes are registered by sending phase 2b messages.  So  *)
(* the array `votes' describing the votes cast by the Nodes is defined *)
(* as follows.                                                             *)
(***************************************************************************)
votes == [a \in Node |->  
           {<<m.bal, m.val>> : m \in {mm \in msgs: /\ mm.type = "2b"
                                                   /\ mm.acc = a }}]
                                                   
                                                  
VotedFor(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorum : \A a \in Q : VotedFor(a, b, v)

\* chosen == {v \in Value : \E b \in Ballot : ChosenAt(b, v)}

\* If two nodes have chosen values, they must be the same.
Safety == \A n,n2 \in Node : 
            (chosen[n] # None /\ chosen[n2] # None) => chosen[n] = chosen[n2]

\* Inv == Cardinality(chosen) <= 1 
Inv == Cardinality(msgs) <= 2

Symmetry == Permutations(Node)


============================================================================