----------------------------- MODULE PaxosStore -----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Value,        \*the set of values
          N,            \*the set of processes
          MCBallot      \* Ballots
       
          
Ballot == 0..MCBallot-1   \*the set of ballot numbers
Acceptor == 1..N          \* the set of Acceotpors

Max(m, n) == IF m > n THEN m ELSE n

 \* A value that not in Ballot for Phase1b of no value                             
NotAnInput == CHOOSE b : b \notin Value
\* A bal not in Ballot
NotABallot == -1

\* maps a proccess to its set of ballots
Bals(p) == {b \in Ballot: b % N = p-1}

\* the set of Quorum, just contain the set that number is (n+1)/2
Quorum == {Q \in SUBSET Acceptor: Cardinality(Q)*2 = N + 1}

\*assumption of quorum to make the definition of quorum
ASSUME QuorumAssumption == /\ \A Q \in Quorum: Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum: Q1 \cap Q2 # {}

StateInTuple == [maxBal: Ballot \cup {NotABallot},
                 maxVBal: Ballot \cup {NotABallot},
                 maxVal: Value \cup {NotAnInput}]

\*init state of the replica
InitDB == [maxBal |-> NotABallot, maxVBal |-> NotABallot, maxVal |-> NotAnInput]

Message ==   [type: {"IssueM", "IssueP"}, from: Acceptor, state: StateInTuple]
        \cup [type: {"Return"}, from: Acceptor, to: Acceptor, state: StateInTuple]

VARIABLES State,     \* State[X][Y]presents state Y from view of X
          msgs,      \* set of messages
          chosen
        \*  votes,
        \*  maxBal

\*maxBal == [a \in Acceptor |-> State[a][a].maxBal]
          
TypeOK == /\ State \in [Acceptor -> [Acceptor -> StateInTuple]]
          /\ msgs \in SUBSET Message
          /\ chosen \in SUBSET Value
        \*  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
        \*  /\ maxBal \in [Acceptor -> Ballot \cup {NotABallot}]

vars == <<State, msgs, chosen>>

Send(m) == msgs' = msgs \cup {m}

IssueM(a, b) == /\ State[a][a].maxBal = NotABallot \/ State[a][a].maxBal < b
                /\ b \in Bals(a)
                /\ State' = [State EXCEPT ![a][a].maxBal = b]
                \*/\ IF State[a][a].maxVBal # NotABallot
                \*     THEN /\ State' = [State EXCEPT ![a][a].maxBal = b,
                \*                                    ![a][a].maxVBal = b]
                \*        /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, State[a][a].maxVal>>}]
                \*     ELSE /\ State' = [State EXCEPT ![a][a].maxBal = b]
                \*        /\ UNCHANGED votes
           \*     /\ maxBal' = [maxBal EXCEPT ![a] = b]
                /\ Send([type |-> "IssueM", from |-> a, state |-> State'[a][a]])                 
                /\ UNCHANGED <<chosen>>

IsMajority(a, b, Q) == \A a1 \in Q: State[a][a1].maxBal = b

FirstToIssueP(b) == \A a \in Acceptor: State[a][a].maxVBal # b
             
IssueP(a, b, v) == /\ \E m \in msgs: /\ m.type = "IssueM"
                                     /\ m.from = a
                   /\ State[a][a].maxBal = b
                   /\ b \in Bals(a)
                   /\ State[a][a].maxVBal < b
                   /\ FirstToIssueP(b)
                   /\ \E Q \in Quorum: 
                      /\ IsMajority(a, b, Q)
                      /\ \/ \A a1 \in Q: State[a][a1].maxVal = NotAnInput  
                         \/ \E s \in Value:
                            /\ s = v
                            /\ \E a2 \in Q: /\ State[a][a2].maxVal = s
                                            /\ \A a3 \in Q \ {a2}: State[a][a2].maxVBal \geq State[a][a3].maxVBal
                   /\ State' = [State EXCEPT ![a][a].maxVBal = b,
                                             ![a][a].maxVal = v]
        \*           /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
        \*           /\ maxBal' = [maxBal EXCEPT ![a] = b]
                   /\ Send([type |-> "IssueP", from |-> a, state |-> State'[a][a]])
                   /\ UNCHANGED <<chosen>>
 
UpdateState(a, from, m) == 
                     LET yxm  == State[a][from].maxBal
                         yxpn == State[a][from].maxVBal
                         yxpv == State[a][from].maxVal
                         
                         xxm  == m.state.maxBal
                         xxpn == m.state.maxVBal
                         xxpv == m.state.maxVal
                         
                         yym  == State[a][a].maxBal
                         yypn == State[a][a].maxVBal
                         yypv == State[a][a].maxVal
                         
                     \*    yxstate == CHOOSE \in StateInTuple
                     \*    yystate == CHOOSE \in StateInTuple
                         
                     IN State' = [State EXCEPT ![a][from] =
                                               CHOOSE yxstate \in StateInTuple:
                                                          /\ IF yxm < xxm
                                                                 THEN yxstate.maxBal = xxm
                                                                 ELSE yxstate.maxBal = yxm
                                                          /\ IF yxpn < xxpn 
                                                                 THEN /\ yxstate.maxVBal = xxpn
                                                                      /\ yxstate.maxVal = xxpv
                                                                 ELSE /\ yxstate.maxVBal = yxpn
                                                                      /\ yxstate.maxVal = yxpv,
                                               ![a][a]   =
                                               CHOOSE yystate \in StateInTuple:
                                                          /\ IF yym < xxm 
                                                                 THEN yystate.maxBal = xxm
                                                                 ELSE yystate.maxBal = yym
                                                          /\ IF yym \leq xxpn
                                                                 THEN /\ yystate.maxVBal = xxpn
                                                                      /\ yystate.maxVal = xxpv
                                                                 ELSE /\ yystate.maxVBal = yypn
                                                                      /\ yystate.maxVal = yypv]
                  (*       /\ IF yym < xxm 
                               THEN maxBal' = [maxBal EXCEPT ![a] = xxm]
                               ELSE UNCHANGED maxBal
                         /\ IF yym \leq xxpn /\ xxpn # NotABallot
                               THEN /\ \/ m.type = "IssueP"
                                       \/ /\ m.type = "Return"
                                          /\ xxpn = xxm
                                    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<xxpn, xxpv>>}]
                               ELSE UNCHANGED <<votes>> 
                    *)

OnMessage(a) == 
             /\ msgs # {}
             /\ \E m \in msgs:
                 \E from \in Acceptor:
                   /\ from = m.from
                   /\ \/ /\ m.type = "Return"
                         /\ m.to = a
                      \/ /\ \/ m.type = "IssueM"
                            \/ m.type = "IssueP"
                         /\ m.from # a
                   /\ UpdateState(a, from, m)
                   /\ IF /\ State[a][a].maxBal < m.state.maxBal \/ State[a][a].maxBal =< m.state.maxVBal
                         THEN \E v \in Value, b \in Ballot:
                               IF \E Q \in Quorum:
                                        \A q \in Q: /\ State'[a][q].maxVBal = b
                                                    /\ State'[a][q].maxVal = v
                                THEN /\ chosen' = chosen \cup {v}
                                ELSE UNCHANGED <<chosen>>
                         ELSE UNCHANGED <<chosen>>   
                   /\ IF State[from][a].maxBal < State'[a][a].maxBal \/ State[from][a].maxVBal < State'[a][a].maxVBal
                        THEN Send([type |-> "Return", from |-> a, to |-> from, state |-> State'[a][a]]) 
                        ELSE UNCHANGED msgs
\*Init State
Init == /\ State = [a \in Acceptor |-> [b \in Acceptor |-> InitDB]] 
        /\ msgs = {}
        /\ chosen = {}
   \*     /\ votes = [a \in Acceptor |-> {}]
   \*     /\ maxBal = [a \in Acceptor |-> NotABallot]
        
                    
Next == \/ \E a \in Acceptor, b \in Ballot: \/ IssueM(a, b)
                                            \/ \E v \in Value: IssueP(a, b, v)
        \/ \E a \in Acceptor: OnMessage(a)                                

Spec == Init /\ [][Next]_vars

Nontriviality == chosen \subseteq Value
 
LSpec == /\ Spec
         /\ \A a1, a2 \in Acceptor: /\ WF_vars(IssueM(a1, MCBallot))
                                    /\ \A v \in Value: WF_vars(IssueP(a1, MCBallot, v) \/ IssueP(a2, MCBallot, v))
                                    /\ WF_vars(OnMessage(a1) \/ OnMessage(a2))

Consistency == Cardinality(chosen) =< 1         
Liveness == <>(chosen # {})   
---------------------------------------------------------------------------
(***************************************************************************
 To verify Spec => Voting, we should define votes and maxBal
 VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
          maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                   \* further votes only in ballots numbered \geq maxBal[a]
 ***************************************************************************)
\*V == INSTANCE Voting with maxBal <- 


\*V == INSTANCE Voting
                       
\*THEOREM Spec => V!Spec
              
=============================================================================
\* Modification History
\* Last modified Sat Dec 01 20:03:45 CST 2018 by stary
\* Last modified Sat Nov 17 16:02:12 GMT+08:00 2018 by pure_
\* Last modified Wed May 09 21:39:31 CST 2018 by dell
\* Created Mon Apr 23 15:47:52 GMT+08:00 2018 by pure_
