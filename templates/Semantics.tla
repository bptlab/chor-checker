---------------- MODULE Semantics ----------------

EXTENDS TLC, Types, Definitions, FiniteSets, Naturals

(*
Problems:
  - there could be an oracle transaction in the same block, so we have to block JUST choreography transactions from happening in the same block
  - we have to do symbolic abstraction somehow for conditions, otherwise the state-space becomes too big
  - maybe also scaling, i.e., when blocktime is 5 seconds but an event calls for a month
*)

(* runtime *)
VARIABLES marking, awaitTransaction, aging, timestamp, oracleValues, messageValues

var == <<marking, awaitTransaction, aging, timestamp, oracleValues, messageValues>>

TypeInvariant ==
  /\ marking \in [ Flows -> BOOLEAN ]
  /\ awaitTransaction \in BOOLEAN
  /\ aging \in [ Flows -> Nat ]
  /\ timestamp \in Nat
  /\ oracleValues \in [ Oracles -> Nat ]
  /\ messageValues \in [ Tasks -> Nat ]

taskIsEnabled(n) ==
  /\ nodeType[n] = Task
  /\ \E f \in incoming(n) : marking[f]

task(n) ==
  /\ taskIsEnabled(n)
  /\ \E fi \in incoming(n) :
       /\ marking[fi]
       /\ marking' = [ f \in DOMAIN marking |->
                           IF f = fi THEN FALSE
                           ELSE IF f \in outgoing(n) THEN TRUE
                           ELSE marking[f] ]
       /\ aging' = [ f \in DOMAIN aging |->
                           IF f = fi \/ f \in outgoing(n) THEN timestamp'
                           ELSE aging[f] ]

oracle(o) == TRUE

gatewayParallel(n) ==
  /\ nodeType[n] = GatewayParallel
  /\ \A f \in incoming(n) : marking[f]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN FALSE
                      ELSE IF f \in outgoing(n) THEN TRUE
                      ELSE marking[f] ]
  /\ aging' = [ f \in DOMAIN aging |->
                      IF f \in incoming(n) \/ f \in outgoing(n) THEN timestamp'
                      ELSE aging[f] ]

eventEnd(n) ==
  /\ nodeType[n] = EventEnd
  /\ \E f \in incoming(n) :
    /\ marking[f]
    /\ marking' = [ marking EXCEPT ![f] = FALSE ]
    /\ aging' = [ aging EXCEPT ![f] = timestamp' ]

stepInternal(n) ==
  CASE nodeType[n] = GatewayParallel -> gatewayParallel(n) /\ awaitTransaction' = FALSE
    [] nodeType[n] = EventEnd -> eventEnd(n) /\ awaitTransaction' = FALSE
    [] OTHER ->
      /\ UNCHANGED <<marking, awaitTransaction, aging>>

stepTransaction(n) ==
  CASE nodeType[n] = Task ->
      /\ task(n)
      /\ awaitTransaction' = FALSE
    [] OTHER -> FALSE

Next == UNCHANGED <<oracleValues, messageValues>> /\
  \/
    /\ timestamp' = timestamp + 1
    /\ awaitTransaction' = TRUE
    /\ UNCHANGED <<marking, aging>>
  \/ \E n \in Nodes :
    /\ UNCHANGED <<timestamp>>
    /\ awaitTransaction => stepTransaction(n)
    /\ ~awaitTransaction => stepInternal(n)

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN TRUE
                     ELSE FALSE ]
  /\ awaitTransaction = TRUE
  /\ aging = [ f \in Flows |-> 0 ]
  /\ timestamp = 0
  /\ oracleValues = [ o \in Oracles |-> 0 ]
  /\ messageValues = [ n \in Tasks |-> 0 ]

Spec == Init /\ [][Next]_var

\*NoTokensLeft ==
\*  \A f \in Flows : <>(\E n \in ContainRel[p] :  marking[n] = 0)

Safety ==
  [](\E f \in Flows : marking[f])

================================================================
