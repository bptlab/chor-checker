---------------- MODULE Semantics ----------------

EXTENDS TLC, FiniteSets, Naturals, Types, Definitions

(*
Problems:
  - we have to do symbolic abstraction somehow for conditions, otherwise the state-space becomes too big
  - maybe time scaling, i.e., when blocktime is 5 seconds but an event calls for a month

Time:
  - We use the block number as our timestamp and assume it is directly proportional to block timestamp.

Token Propagation:
  - Local: tokens get propagated only from the called task
  - Global: all tokens in the entire model get propagated

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
isEnabled(n) ==
  CASE nodeType[n] = GatewayParallel -> \A f \in incoming(n) : marking[f][1]
    [] nodeType[n] = EventIntermediate -> \E f \in incoming(n) : marking[f][1] /\ evaluateIntermediateEvent(n, f, marking, timestamp, oracleValues, messageValues)
    [] OTHER -> \E f \in incoming(n) : marking[f][1]

enabledNodes == { n \in Nodes \ Tasks : isEnabled(n) /\ nodeType[n] /= GatewayEvent }

executeNode(n) ==
  /\ UNCHANGED <<oracleValues, messageValues, curTx>>
  /\ CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
       [] nodeType[n] = GatewayExclusive -> gatewayExclusive(n)
       [] nodeType[n] = EventEnd -> eventEnd(n)
       [] nodeType[n] = EventIntermediate -> eventIntermediate(n)
       [] OTHER -> FALSE

(* end transactions *)
endTx ==
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = <<timestamp, Empty, Empty, NoPayload>>

(* start transactions *)
doStartTaskTx(t, reset) ==
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in reset THEN <<FALSE, timestamp>>
                      ELSE IF f \in outgoing(t) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]
  /\ \E mv \in MessageDomain[t] :
    /\ curTx' = <<timestamp, TaskTx, t, mv>>
    /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]
  /\ UNCHANGED <<oracleValues, timestamp>>

startTaskTx ==
  \E t \in Tasks : \E fi \in incoming(t) : LET predecessor == source[fi] IN
    \/ \* direct enablement - _fi_ (_t_)
      /\ marking[fi][1]
      /\ doStartTaskTx(t, {fi})
    \/ \* indirect enablement - _fii_ (g) fi | fj (_t_ | sibling...)
      /\ nodeType[predecessor] = GatewayEvent
      /\ \E fii \in incoming(predecessor) :
        /\ marking[fii][1] \* predecessor is an enabled event-based gateway
        /\ ~\E fj \in outgoing(predecessor) : LET sibling == target[fj] IN
          /\ t /= sibling
          /\ nodeType[sibling] = EventIntermediate
          /\ \E history \in marking[fii][2]..timestamp :
            /\ evaluateIntermediateEvent(target[fj], fii, marking, history, oracleValues, messageValues)
        /\ doStartTaskTx(t, {fi, fii})
    \/
      /\ nodeType[predecessor] = EventIntermediate
      /\ \E fii \in incoming(predecessor) : LET prepredecessor == source[fii] IN
        \/ \* conditional enablement - _fii_ (e) fi (_t_)
          /\ marking[fii][1]
          /\ evaluateIntermediateEvent(predecessor, fii, marking, timestamp, oracleValues, messageValues)
          /\ doStartTaskTx(t, {fi, fii})
        \/ \* conditional indirect enablement - _fiii_ (g) fii (e...) fi (_t_)
          /\ nodeType[prepredecessor] = GatewayEvent
          /\ \E fiii \in incoming(prepredecessor) :
            /\ marking[fiii][1]
            /\ evaluateIntermediateEvent(predecessor, fiii, marking, timestamp, oracleValues, messageValues)
            (* TODO AND NO EARLIER ENABLED *)
            /\ doStartTaskTx(t, {fi, fii, fiii})

startOracleTx ==
  \E o \in Oracles : \E v \in OracleDomain[o] :
    /\ oracleValues' = [ oracleValues EXCEPT ![o] = <<v, timestamp>> ]
    /\ curTx' = <<timestamp, OracleTx, o, v>>
  /\ UNCHANGED <<marking, messageValues, timestamp>>

(* process transactions *)
processTaskTx ==
  /\ curTx[2] = TaskTx
  /\ UNCHANGED timestamp
  /\ IF Cardinality(enabledNodes) > 0
     THEN \E n \in enabledNodes : executeNode(n)
     ELSE endTx

processOracleTx ==
  /\ curTx[2] = OracleTx
  /\ UNCHANGED timestamp
  /\ IF PUSH_ORACLES /\ Cardinality(enabledNodes) > 0
     THEN \E n \in enabledNodes : executeNode(n)
     ELSE endTx

processDeployTx ==
  /\ curTx[2] = DeployTx
  /\ IF Cardinality(enabledNodes) > 0
     THEN UNCHANGED timestamp /\ \E n \in enabledNodes : executeNode(n)
     ELSE timestamp' = timestamp + 1 /\ endTx

(* timestep processing *)
timestep ==
  /\ timestamp < MAX_TIMESTAMP
  /\ UNCHANGED <<marking, oracleValues, messageValues, curTx>>
  /\ timestamp' = timestamp + 1

(* transition system *)
Next ==
  \/ processTaskTx
  \/ processDeployTx
  \/ processOracleTx
  \/
    /\ curTx[2] = Empty
    /\
      \/ startTaskTx
      \/ startOracleTx
      \/ timestep

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN <<TRUE, 0>>
                     ELSE <<FALSE, 0>> ]
  /\ oracleValues \in { ov \in [ Oracles -> AllOracleDomains \X { 0 } ] : \A o \in Oracles : ov[o][1] \in OracleDomain[o] }
  /\ messageValues \in { mv \in [ Tasks -> AllMessageDomains ] : \A t \in Tasks : mv[t] = NoPayload }
  /\ timestamp = 0
  /\ curTx = <<0, DeployTx, Empty, NoPayload>>

Fairness == WF_var(startOracleTx) /\ WF_var(startTaskTx) /\ WF_var(timestep)

Spec == Init /\ [][Next]_var /\ Fairness

TypeInvariant ==
  /\ marking \in [ Flows -> BOOLEAN \X Nat ]
  /\ oracleValues \in [ Oracles -> AllOracleDomains \X Nat ]
  /\ \A o \in Oracles : oracleValues[o][1] \in OracleDomain[o]
  /\ messageValues \in [ Tasks -> AllMessageDomains ]
  /\ \A t \in Tasks : messageValues[t] \in { NoPayload } \union MessageDomain[t]
  /\ timestamp \in 0..MAX_TIMESTAMP
  /\ curTx \in Nat                                     (* timestamp *)
            \X TxType                                  (* transaction type *)
            \X (Tasks \union Oracles \union { Empty }) (* transaction target *)
            \X PayloadDomain                           (* payload *)

================================================================
