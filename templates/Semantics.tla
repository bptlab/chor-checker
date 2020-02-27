---------------- MODULE Semantics ----------------

EXTENDS TLC, Types, Definitions, FiniteSets, Naturals

(*
Problems:
  - there could be an oracle transaction in the same block, so we have to block JUST choreography transactions from happening in the same block
  - we have to do symbolic abstraction somehow for conditions, otherwise the state-space becomes too big
  - maybe also scaling, i.e., when blocktime is 5 seconds but an event calls for a month

Idea:
  - create separate start/end transaction states
  - a transaction is locked until there is no more work to do inside it
  - that way we do not have to cram everything into a single transition
*)

(* configuration *)
VARIABLES marking, aging, oracleValues, messageValues, timestamp, curTx

var == <<marking, aging, oracleValues, messageValues, timestamp, curTx>>

TypeInvariant ==
  /\ marking \in [ Flows -> BOOLEAN ]
  /\ aging \in [ Flows -> Nat ]
  /\ oracleValues \in [ Oracles -> Nat ]
  /\ messageValues \in [ Tasks -> Nat ]
  /\ timestamp \in Nat
  /\ curTx \in TxType \X Nat \* add payload, could be different for task/oracle tx *\

(* transaction processing *)
gatewayParallel(n) ==
  /\ \A f \in incoming(n) : marking[f]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN FALSE
                      ELSE IF f \in outgoing(n) THEN TRUE
                      ELSE marking[f] ]
  /\ aging' = [ f \in DOMAIN aging |->
                      IF f \in incoming(n) \/ f \in outgoing(n) THEN timestamp'
                      ELSE aging[f] ]

eventEnd(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f]
    /\ marking' = [ marking EXCEPT ![f] = FALSE ]
    /\ aging' = [ aging EXCEPT ![f] = timestamp' ]

(* propagate flow *)
propagateFlow ==
  /\ UNCHANGED <<oracleValues, messageValues, curTx>>
  /\ \E n \in Nodes \ Tasks :
       CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
         [] nodeType[n] = EventEnd -> eventEnd(n)
         [] OTHER -> FALSE

(* end transactions *)
endTx ==
  /\ UNCHANGED <<marking, aging, oracleValues, messageValues>>
  /\ curTx' = <<NoTx, timestamp>>

(* start transactions *)
startChoreoTx ==
  \E t \in Tasks :
    \E fi \in incoming(t) :
      /\ marking[fi]
      /\ marking' = [ f \in DOMAIN marking |->
                          IF f = fi THEN FALSE
                          ELSE IF f \in outgoing(t) THEN TRUE
                          ELSE marking[f] ]
      /\ aging' = [ f \in DOMAIN aging |->
                          IF f = fi \/ f \in outgoing(t) THEN timestamp
                          ELSE aging[f] ]
      /\ UNCHANGED oracleValues
      /\ UNCHANGED messageValues
      /\ UNCHANGED timestamp
      /\ curTx' = <<ChoreoTx, timestamp>>

startOracleTx == FALSE /\ UNCHANGED timestamp \* TODO *\

(* timestep processing *)
timestep ==
  /\ UNCHANGED <<marking, aging, oracleValues, messageValues, curTx>>
  /\ timestamp' = timestamp + 1

(* transition system *)
Next ==
  IF curTx[1] = NoTx THEN
    \/ startChoreoTx
    \/ startOracleTx
    \/ timestep
  ELSE
    /\ UNCHANGED timestamp
    /\ propagateFlow
      \/ endTx

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN TRUE
                     ELSE FALSE ]
  /\ aging = [ f \in Flows |-> 0 ]
  /\ oracleValues = [ o \in Oracles |-> 0 ]
  /\ messageValues = [ n \in Tasks |-> 0 ]
  /\ timestamp = 0
  /\ curTx = <<NoTx, 0>>

Spec == Init /\ [][Next]_var

(* properties *)
Safety ==
  [](\E f \in Flows : marking[f])

================================================================
