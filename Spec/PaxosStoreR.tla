---------------------------- MODULE PaxosStoreR ----------------------------
EXTENDS PaxosStore

VARIABLE voted
varsR == <<vars, voted>>

InitR == Init /\ (voted = [a \in Acceptor |-> {}])

IssueMR(a, b) == /\ IssueM(a, b)
                 /\ voted' = voted
           
IssuePR(a, b, v) == /\ IssueP(a, b, v)
                    /\ voted' = [voted EXCEPT ![a] = @ \cup {<<b, v>>}]
                    
OnMessageR(a) == /\ OnMessage(a)
                 /\ IF State'[a][a].maxVBal # NotABallot
                        THEN voted' = [voted EXCEPT ![a] = @ \cup {<<State'[a][a].maxVBal, State[a][a]'.maxVal>>}]
                        ELSE UNCHANGED voted
                        
NextR == \/ \E a \in Acceptor, b \in Ballot: \/ IssueMR(a, b)
                                             \/ \E v \in Value: IssuePR(a, b, v)
         \/ \E a \in Acceptor: OnMessageR(a)                                

SpecR == InitR /\ [][NextR]_varsR

(***************************************************************************
  To verify Spec => Voting, we should define votes and maxBal
          votes,   \* votes[a] is the set of votes cast by acceptor a
          maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                   \* further votes only in ballots numbered \geq maxBal[a]
 ***************************************************************************)

V == INSTANCE Voting WITH votes  <- voted,
                          maxBal <- [a \in Acceptor |-> State[a][a].maxBal]

THEOREM Spec => V!Spec
=============================================================================
\* Modification History
\* Last modified Sat Dec 01 20:52:35 CST 2018 by stary
\* Created Sat Dec 01 20:04:16 CST 2018 by stary
