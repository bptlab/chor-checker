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
                        IF ff = f THEN <<FALSE, marking[f][2]>>
                        ELSE IF ff \in outgoing(n) THEN <<TRUE, timestamp>>
                        ELSE marking[ff] ]

gatewayParallel(n) ==
  /\ \A f \in incoming(n) : marking[f][1]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN <<FALSE, marking[f][2]>>
                      ELSE IF f \in outgoing(n) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]

gatewayExclusive(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ LET enabled == { fo \in outgoing(n) : evaluateFlow(fo, oracleValues, messageValues) } IN
      IF Cardinality(enabled) > 0 THEN
        /\ \E ff \in enabled : 
          /\ marking' = [ marking EXCEPT ![f] = <<FALSE, @[2]>>, ![ff] = <<TRUE, timestamp>> ]
      ELSE
        /\ marking' = [ marking EXCEPT ![f] = <<FALSE, @[2]>>, ![defaultFlow[n]] = <<TRUE, timestamp>> ]

eventEnd(n) ==
  /\ \E f \in incoming(n) :
    /\ marking[f][1]
    /\ marking' = [ marking EXCEPT ![f] = <<FALSE, @[2]>> ]

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

(* start transactions *)
doStartTaskTx(t, consume, touch) ==
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f = consume THEN <<FALSE, marking[f][2]>>
                      ELSE IF f \in touch THEN <<FALSE, timestamp>>
                      ELSE IF f \in outgoing(t) THEN <<TRUE, timestamp>>
                      ELSE marking[f] ]
  /\ \E mv \in MessageDomain[t] :
    /\ curTx' = <<timestamp, TaskTx, t, mv>>
    /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]
  /\ UNCHANGED <<oracleValues, timestamp>>

startTaskTx ==
  \E t \in Tasks : \E fi \in incoming(t) : LET predecessor == source[fi] IN

    (* Direct Enablement.
       A task is directly enabled, if there is a token on any incoming sequence flow.
       Structure: _fi_ (t) *)
    \/
      /\ marking[fi][1]
      /\ doStartTaskTx(t, fi, {})

    (* Indirect Enablement.
       A task is indirectly enabled, if it follows an event-based gateway and that
       gateway is enabled. Additionally, no other successor of the event-based
       gateway may have been enabled before, as in that case that node has to fire.
       Structure: _fii_ (gw) fi | fj (t | sibling) *)
    \/
      /\ nodeType[predecessor] = GatewayEvent
      /\ \E fii \in incoming(predecessor) :
        /\ marking[fii][1] \* predecessor is an enabled event-based gateway
        /\ ~\E fj \in outgoing(predecessor) : LET sibling == target[fj] IN
          /\ t /= sibling
          /\ nodeType[sibling] = EventIntermediate
          /\ \E history \in marking[fii][2]..timestamp :
            /\ evaluateIntermediateEvent(sibling, fii, marking, history, oracleValues, messageValues)
        /\ doStartTaskTx(t, fii, {fi})

    (* Conditional Enablement.
       A task is conditionally enabled if it follows an intermediate catch event
       that is enabled and can fire.
       Structure: _fii_ (e) fi (t) *)
    \/
      /\ nodeType[predecessor] = EventIntermediate
      /\ \E fii \in incoming(predecessor) : LET prepredecessor == source[fii] IN
        \/
          /\ marking[fii][1]
          /\ evaluateIntermediateEvent(predecessor, fii, marking, timestamp, oracleValues, messageValues)
          /\ doStartTaskTx(t, fii, {fi})

    (* Indirect Conditional Enablement.
       A task is indirectly conditionally enabled if it follows an intermediate catch
       event that is enabled via an event-based gateway and can fire.
       Additionally, no other successor of the event-based gateway should have been
       enabled since an earlier point in time than this one. If that is the case, the
       other event has precedence.
       Structure: _fiii_ (g) fii (e | presibling) fi (t) *)
        \/
          /\ nodeType[prepredecessor] = GatewayEvent
          /\ \E fiii \in incoming(prepredecessor) :
            /\ marking[fiii][1]
            /\ evaluateIntermediateEvent(predecessor, fiii, marking, timestamp, oracleValues, messageValues)
            /\ ~\E fij \in outgoing(prepredecessor) : LET presibling == target[fij] IN
              /\ predecessor /= presibling
              /\ nodeType[presibling] = EventIntermediate
              /\ \E history \in marking[fiii][2]..timestamp :
                /\ evaluateIntermediateEvent(presibling, fiii, marking, history, oracleValues, messageValues)
                /\ ~\E history2 \in marking[fiii][2]..history :
                  evaluateIntermediateEvent(predecessor, fiii, marking, history2, oracleValues, messageValues)
            /\ doStartTaskTx(t, fiii, {fi, fii})

startOracleTx ==
  \E o \in Oracles : \E v \in OracleDomain[o] :
    /\ oracleValues' = [ oracleValues EXCEPT ![o] = <<v, timestamp>> ]
    /\ curTx' = <<timestamp, OracleTx, o, v>>
  /\ UNCHANGED <<marking, messageValues, timestamp>>

(* process transactions *)
canEndTx ==
  CASE curTx[2] = TaskTx -> Cardinality(enabledNodes) = 0
    [] curTx[2] = OracleTx -> ~PUSH_ORACLES \/ Cardinality(enabledNodes) = 0
    [] curTx[2] = DeployTx -> Cardinality(enabledNodes) = 0
    [] OTHER -> TRUE

processTaskTx ==
  /\ curTx[2] = TaskTx
  /\ UNCHANGED timestamp
  /\ \E n \in enabledNodes : executeNode(n)

processOracleTx ==
  /\ curTx[2] = OracleTx
  /\ UNCHANGED timestamp
  /\ PUSH_ORACLES
  /\ \E n \in enabledNodes : executeNode(n)

processDeployTx ==
  /\ curTx[2] = DeployTx
  /\ UNCHANGED timestamp
  /\ \E n \in enabledNodes : executeNode(n)

(* timestep processing *)
timestep ==
  /\ timestamp < MAX_TIMESTAMP
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = <<timestamp + 1, Empty, Empty, NoPayload>>
  /\ timestamp' = timestamp + 1

(* transition system *)
Next ==
  \/ processTaskTx
  \/ processDeployTx
  \/ processOracleTx
  \/
    /\ canEndTx
    /\
      \/ curTx[2] /= DeployTx \* require timestep after deploy
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
