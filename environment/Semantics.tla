---------------- MODULE Semantics ----------------

EXTENDS TLC, FiniteSets, Integers, Naturals, Types, Definitions

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

PAST == -1

hasFinished == Cardinality(marking) = 0

flowEnabled(f) == \E m \in marking : m[1] = f

(* transaction processing *)
eventIntermediate(n) ==
  /\ \E m \in marking : LET f == m[1] IN
    /\ f \in incoming(n)
    /\ evaluateIntermediateEvent(n, m, marking, timestamp, oracleValues, messageValues)
    /\ marking' = (marking \ { m }) \union (outgoing(n) \X { timestamp })

gatewayParallel(n) ==
  /\ LET inMarking == { <<f, c>> \in marking : f \in incoming(n) } IN
    /\ Cardinality(incoming(n)) = Cardinality(inMarking)
    /\ marking' = (marking \ inMarking) \union (outgoing(n) \X { timestamp })

gatewayExclusive(n) ==
  /\ \E m \in marking : LET f == m[1] IN
    /\ f \in incoming(n)
    /\ LET enabledFlows == { fo \in outgoing(n) : evaluateFlow(fo, oracleValues, messageValues) } IN
      IF Cardinality(enabledFlows) > 0 THEN
        /\ \E ff \in enabledFlows :
          /\ marking' = (marking \ { m }) \union { <<ff, timestamp>> }
      ELSE
        /\ marking' = (marking \ { m }) \union { <<defaultFlow[n], timestamp>> }

eventEnd(n) ==
  /\ \E m \in marking : LET f == m[1] IN
    /\ f \in incoming(n)
    /\ marking' = marking \ { m }

(* propagate flow *)
isEnabled(n) ==
  CASE nodeType[n] = GatewayParallel -> \A f \in incoming(n) : flowEnabled(f)
    [] nodeType[n] = EventIntermediate -> \E m \in marking : LET f == m[1] IN
                                       /\ f \in incoming(n)
                                       /\ evaluateIntermediateEvent(n, m, marking, timestamp, oracleValues, messageValues)
    [] OTHER -> \E f \in incoming(n) : flowEnabled(f)

enabledNodes == { n \in Nodes \ Tasks : isEnabled(n) /\ nodeType[n] /= GatewayEvent }

executeNode(n) ==
  /\ UNCHANGED <<oracleValues, messageValues, curTx>>
  /\ CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
       [] nodeType[n] = GatewayExclusive -> gatewayExclusive(n)
       [] nodeType[n] = EventEnd -> eventEnd(n)
       [] nodeType[n] = EventIntermediate -> eventIntermediate(n)
       [] OTHER -> FALSE

(* start transactions *)
doStartTaskTx(t, consume) ==
  /\ marking' = (marking \ { consume }) \union (outgoing(t) \X { timestamp })
  /\ \E mv \in MessageDomain[t] :
    /\ curTx' = <<timestamp, TaskTx, t, mv>>
    /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]

startTaskTx ==
  /\ UNCHANGED <<oracleValues, timestamp>>
  /\ \E t \in Tasks :
    /\ \E fi \in incoming(t) : LET predecessor == source[fi] IN

      (* Direct Enablement.
        A task is directly enabled, if there is a token on any incoming sequence flow.
        Structure: _fi_ (t) *)
      \/
        /\ \E mi \in marking :
          /\ mi[1] = fi
          /\ doStartTaskTx(t, mi)

      (* Indirect Enablement.
        A task is indirectly enabled, if it follows an event-based gateway and that
        gateway is enabled. Additionally, no other successor of the event-based
        gateway may have been enabled before, as in that case that node has to fire.
        Structure: _fii_ (gw) fi | fj (t | sibling) *)
      \/
        /\ nodeType[predecessor] = GatewayEvent
        /\ \E fii \in incoming(predecessor) :
          /\ \E mii \in marking :
            /\ mii[1] = fii \* predecessor is an enabled event-based gateway
            /\ ~\E fj \in outgoing(predecessor) : LET sibling == target[fj] IN
              /\ t /= sibling
              /\ nodeType[sibling] = EventIntermediate
              /\ \E history \in mii[2]..timestamp :
                /\ evaluateIntermediateEvent(sibling, mii, marking, history, oracleValues, messageValues)
            /\ doStartTaskTx(t, mii)

      (* Conditional Enablement.
        A task is conditionally enabled if it follows an intermediate catch event
        that is enabled and can fire.
        Structure: _fii_ (e) fi (t) *)
      \/
        /\ nodeType[predecessor] = EventIntermediate
        /\ \E fii \in incoming(predecessor) : LET prepredecessor == source[fii] IN
          \/
            /\ \E mii \in marking :
              /\ mii[1] = fii
              /\ evaluateIntermediateEvent(predecessor, mii, marking, timestamp, oracleValues, messageValues)
              /\ doStartTaskTx(t, mii)

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
              /\ \E miii \in marking :
                /\ miii[1] = fiii
                /\ evaluateIntermediateEvent(predecessor, miii, marking, timestamp, oracleValues, messageValues)
                /\ ~\E fij \in outgoing(prepredecessor) : LET presibling == target[fij] IN
                  /\ predecessor /= presibling
                  /\ nodeType[presibling] = EventIntermediate
                  /\ \E history \in miii[2]..timestamp :
                    /\ evaluateIntermediateEvent(presibling, miii, marking, history, oracleValues, messageValues)
                    /\ ~\E history2 \in miii[2]..history :
                      evaluateIntermediateEvent(predecessor, miii, marking, history2, oracleValues, messageValues)
                /\ doStartTaskTx(t, miii)

startOracleTx ==
  \E o \in Oracles :
    /\ oracleValues[o][2] < timestamp \* only allow one change per timestep
    /\ \E v \in OracleDomain[o] :
      /\ oracleValues' = [ oracleValues EXCEPT ![o] = <<v, timestamp>> ]
      /\ curTx' = <<timestamp, OracleTx, o, v>>
  /\ UNCHANGED <<marking, messageValues, timestamp>>

(* timestep processing *)
timestep ==
  /\ timestamp < MAX_TIMESTAMP
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = <<timestamp + 1, Empty, Empty, NoPayload>>
  /\ timestamp' = timestamp + 1

(* process transactions *)
canStartNewTx ==
  CASE curTx[2] = TaskTx -> Cardinality(enabledNodes) = 0
    [] curTx[2] = OracleTx -> ~PUSH_ORACLES \/ Cardinality(enabledNodes) = 0
    [] curTx[2] = DeployTx -> FALSE \* deploy tx ends itself with a timestep
    [] OTHER -> TRUE

processTaskTx ==
  /\ curTx[2] = TaskTx
  /\ UNCHANGED timestamp
  /\ \E n \in enabledNodes : executeNode(n)

processOracleTx ==
  /\ curTx[2] = OracleTx
  /\ PUSH_ORACLES
  /\ UNCHANGED timestamp
  /\ \E n \in enabledNodes : executeNode(n)

processDeployTx ==
  /\ curTx[2] = DeployTx
  /\ IF Cardinality(enabledNodes) > 0
     THEN /\ UNCHANGED timestamp
          /\ \E n \in enabledNodes : executeNode(n)
     ELSE /\ timestep \* end with a timestep

(* transition system *)
Next ==
  /\ ~hasFinished
  /\
    \/ processTaskTx
    \/ processDeployTx
    \/ processOracleTx
    \/
      /\ canStartNewTx
      /\
        \/ startTaskTx
        \/ startOracleTx
        \/ timestep

Init ==
  /\ marking = { <<f, c>> \in Flows \X { 0 } : nodeType[source[f]] = EventStart }
  /\ oracleValues \in {
       ov \in [ Oracles -> AllOracleDomains \X { PAST } ] :
         \A o \in Oracles : ov[o][1] \in OracleDomain[o]
     }
  /\ messageValues \in {
       mv \in [ Tasks -> AllMessageDomains ] :
         \A t \in Tasks : mv[t] = NoPayload
     }
  /\ timestamp = 0
  /\ curTx = <<0, DeployTx, Empty, NoPayload>>

Fairness ==
  /\ WF_var(processTaskTx)
  /\ WF_var(processOracleTx)
  /\ WF_var(processDeployTx)
  /\ WF_var(startOracleTx)
  /\ WF_var(startTaskTx)
  /\ WF_var(timestep)

Spec == Init /\ [][Next]_var /\ Fairness

TypeInvariant ==
  /\ marking \subseteq Flows \X Nat
  /\ \A m1 \in marking : ~\E m2 \in marking : (m1[1] = m2[1] /\ m1[2] /= m2[2]) \* 1-safety
  /\ oracleValues \in [ Oracles -> AllOracleDomains \X (Nat \union { PAST }) ]
  /\ \A o \in Oracles : oracleValues[o][1] \in OracleDomain[o]
  /\ messageValues \in [ Tasks -> AllMessageDomains ]
  /\ \A t \in Tasks : messageValues[t] \in { NoPayload } \union MessageDomain[t]
  /\ timestamp \in 0..MAX_TIMESTAMP
  /\ curTx \in Nat                                     (* timestamp *)
            \X TxType                                  (* transaction type *)
            \X (Tasks \union Oracles \union { Empty }) (* transaction target *)
            \X PayloadDomain                           (* payload *)

================================================================
