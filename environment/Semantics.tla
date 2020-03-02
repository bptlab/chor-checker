---------------- MODULE Semantics ----------------

EXTENDS TLC, FiniteSets, Naturals, Types, Definitions

(*
Problems:
  - we have to do symbolic abstraction somehow for conditions, otherwise the state-space becomes too big
  - maybe time scaling, i.e., when blocktime is 5 seconds but an event calls for a month
  - propagate flow always propagates globally... so we would have to implement a set or something that keeps track of the flows to propagate during the current tx to avoid global side-effects

Optimization:
  - allow oracles to change only once per timestep
*)

(* configuration *)
VARIABLES marking, oracleValues, messageValues, timestamp, curTx

var == <<marking, oracleValues, messageValues, timestamp, curTx>>

(* transaction processing *)
eventIntermediate(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ evaluateIntermediateEvent(n, f, marking, timestamp, oracleValues, messageValues)
    /\ marking' = [ ff \in DOMAIN marking |->
                        IF ff = f THEN <<FALSE, timestamp>>
                        ELSE IF ff \in outgoing(n) THEN <<TRUE, timestamp>>
                        ELSE marking[ff] ]

\* TODO add gateway handling when first encountered
\* gatewayEvent(n) ==
\*   /\ \E f \in incoming(n) :
\*     /\ marking[f][1]

gatewayParallel(n) ==
  /\ \A f \in incoming(n) : marking[f][1]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN <<FALSE, timestamp>>
                      ELSE IF f \in outgoing(n) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]

gatewayExclusive(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ LET enabled == { fo \in outgoing(n) : evaluateFlow(fo, oracleValues, messageValues) } IN
      IF Cardinality(enabled) > 0 THEN
        /\ \E ff \in enabled : 
          /\ marking' = [ marking EXCEPT ![f] = <<FALSE, timestamp>>, ![ff] = <<TRUE, timestamp>> ]
      ELSE
        /\ marking' = [ marking EXCEPT ![f] = <<FALSE, timestamp>>, ![defaultFlow[n]] = <<TRUE, timestamp>> ]

eventEnd(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ marking' = [ marking EXCEPT ![f] = <<FALSE, timestamp>> ]

(* propagate flow *)
propagateFlow ==
  /\ UNCHANGED <<oracleValues, messageValues, curTx>>
  /\ \E n \in Nodes \ Tasks :
       CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
         [] nodeType[n] = GatewayExclusive -> gatewayExclusive(n)
         [] nodeType[n] = EventEnd -> eventEnd(n)
         [] nodeType[n] = EventIntermediate -> eventIntermediate(n)
         [] OTHER -> FALSE

(* end transactions *)
endTx ==
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = <<NoTx, timestamp, NoPayload>>

(* start transactions *)
doStartChoreoTx(t, reset) ==
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in reset THEN <<FALSE, timestamp>>
                      ELSE IF f \in outgoing(t) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]
  /\ \E mv \in MessageDomain[t] :
    /\ curTx' = <<ChoreoTx, timestamp, mv>>
    /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]
  /\ UNCHANGED <<oracleValues, timestamp>>

startChoreoTx ==
  \E t \in Tasks :
    \* direct enablement
    \/ \E fi \in incoming(t) :
      /\ marking[fi][1]
      /\ doStartChoreoTx(t, {fi})
    \* indirect enablement
    \/ \E fi \in incoming(t) :
      /\ nodeType[source[fi]] = GatewayEvent
      /\ \E fii \in incoming(source[fi]) :
        /\ marking[fii][1]
        /\ doStartChoreoTx(t, {fi, fii})
    \* conditional enablement
    \/ \E fi \in incoming(t) :
      /\ nodeType[source[fi]] = EventIntermediate
      /\ \E fii \in incoming(source[fi]) :
        /\ marking[fii][1]
        /\ evaluateIntermediateEvent(source[fi], fii, marking, timestamp, oracleValues, messageValues)
        /\ doStartChoreoTx(t, {fi, fii})

startOracleTx ==
  \E o \in Oracles : \E v \in OracleDomain[o] :
    /\ oracleValues' = [ oracleValues EXCEPT ![o] = v ]
    /\ curTx' = <<OracleTx, timestamp, v>>
  /\ UNCHANGED <<marking, messageValues, timestamp>>

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
    /\ IF PUSH_ORACLES \/ curTx[1] = ChoreoTx
       THEN propagateFlow \/ endTx
       ELSE endTx

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN <<TRUE, 0>>
                     ELSE <<FALSE, 0>> ]
  /\ oracleValues \in { ov \in [ Oracles -> AllOracleDomains ] : \A o \in Oracles : ov[o] \in OracleDomain[o] }
  /\ messageValues \in { mv \in [ Tasks -> AllMessageDomains ] : \A t \in Tasks : mv[t] \in MessageDomain[t] }
  /\ timestamp = 0
  /\ curTx = <<NoTx, 0, NoPayload>>

Spec == Init /\ [][Next]_var

TypeInvariant ==
  /\ marking \in [ Flows -> BOOLEAN \X Nat ]
  /\ oracleValues \in [ Oracles -> AllOracleDomains ]
  /\ \A o \in Oracles : oracleValues[o] \in OracleDomain[o]
  /\ messageValues \in [ Tasks -> AllMessageDomains ]
  /\ \A t \in Tasks : messageValues[t] \in MessageDomain[t]
  /\ timestamp \in Nat
  /\ curTx \in TxType \X Nat \X PayloadDomain \* restrict payloads to allowed ones for each oracle/choreo call *\

(* properties *)
Safety ==
  [](\E f \in Flows : marking[f][1])

================================================================
