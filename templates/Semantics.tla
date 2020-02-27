---------------- MODULE Semantics ----------------

EXTENDS TLC, Types, Definitions, FiniteSets, Naturals

(*
Problems:
  - we have to do symbolic abstraction somehow for conditions, otherwise the state-space becomes too big
  - maybe time scaling, i.e., when blocktime is 5 seconds but an event calls for a month

Idea:
  - create separate start/end transaction states
  - a transaction is locked until there is no more work to do inside it
  - that way we do not have to cram everything into a single transition

Optimization:
  - allow oracles to change only once per timestep
*)

(* configuration *)
VARIABLES marking, oracleValues, messageValues, timestamp, curTx

var == <<marking, oracleValues, messageValues, timestamp, curTx>>

(* move this to choreography.tla somehow so we only have to generate one file *)
evaluateIntermediateEvent(n, f) ==
  CASE n = "ET" -> timestamp - marking[f][2] = 2
    [] n = "EC" -> oracleValues["WEATHER"] = 9
    [] OTHER -> FALSE

TypeInvariant ==
  /\ marking \in [ Flows -> BOOLEAN \X Nat ]
  /\ oracleValues \in [ Oracles -> AllOracleDomains ]
  /\ \A o \in Oracles : oracleValues[o] \in OracleDomain[o]
  /\ messageValues \in [ Tasks -> Nat ]
  /\ timestamp \in Nat
  /\ curTx \in TxType \X Nat \X PayloadDomain \* restrict payloads to allowed ones for each oracle/choreo call *\

(* transaction processing *)
eventIntermediate(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ evaluateIntermediateEvent(n, f)
    /\ marking' = [ ff \in DOMAIN marking |->
                        IF ff = f THEN <<FALSE, timestamp>>
                        ELSE IF ff \in outgoing(n) THEN <<TRUE, timestamp>>
                        ELSE marking[ff] ]

gatewayParallel(n) ==
  /\ \A f \in incoming(n) : marking[f][1]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN <<FALSE, timestamp>>
                      ELSE IF f \in outgoing(n) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]

eventEnd(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ marking' = [ marking EXCEPT ![f] = <<FALSE, timestamp>> ]

(* propagate flow *)
propagateFlow ==
  /\ UNCHANGED <<oracleValues, messageValues, curTx>>
  /\ \E n \in Nodes \ Tasks :
       CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
         [] nodeType[n] = EventEnd -> eventEnd(n)
         [] nodeType[n] \in EventIntermediateType -> eventIntermediate(n)
         [] OTHER -> FALSE

(* end transactions *)
endTx ==
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = <<NoTx, timestamp, NoPayload>>

(* start transactions *)
startChoreoTx ==
  \E t \in Tasks :
    \E fi \in incoming(t) :
      /\ marking[fi][1]
      /\ marking' = [ f \in DOMAIN marking |->
                          IF f = fi THEN <<FALSE, timestamp>>
                          ELSE IF f \in outgoing(t) THEN <<TRUE, timestamp>>
                          ELSE marking[f] ]
      /\ \E mv \in MessageDomain :
        /\ curTx' = <<ChoreoTx, timestamp, mv>>
        /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]
      /\ UNCHANGED <<oracleValues, timestamp>>

startOracleTx ==
  \E o \in Oracles : \E v \in OracleDomain[o] :
    /\ oracleValues' = [ oracleValues EXCEPT ![o] = v ]
    /\ curTx' = <<OracleTx, timestamp, v>>
  /\ UNCHANGED <<marking, oracleValues, messageValues, timestamp>>

(* timestep processing *)
timestep ==
  /\ UNCHANGED <<marking, oracleValues, messageValues, curTx>>
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
                     IF nodeType[source[f]] = EventStart THEN <<TRUE, 0>>
                     ELSE <<FALSE, 0>> ]
  /\ oracleValues \in { ov \in [ Oracles -> AllOracleDomains ] : \A o \in Oracles : ov[o] \in OracleDomain[o] }
  /\ messageValues = [ n \in Tasks |-> 0 ]
  /\ timestamp = 0
  /\ curTx = <<NoTx, 0, NoPayload>>

Spec == Init /\ [][Next]_var

(* properties *)
Safety ==
  [](\E f \in Flows : marking[f][1])

================================================================
