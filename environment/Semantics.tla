---------------- MODULE Semantics ----------------

EXTENDS TLC, FiniteSets, Integers, Naturals, Types, Definitions

VARIABLES marking, oracleValues, messageValues, timestamp, curTx
var == <<marking, oracleValues, messageValues, timestamp, curTx>>

(* ---------------------- *)
(* --- Node Execution --- *)
(* ---------------------- *)

modifyMarking(consume, produce) ==
  /\ marking' = (marking \ { m \in marking : m[1] \in consume })
                \union { <<f, timestamp>> : f \in produce }
  /\ curTx' = [curTx EXCEPT !.touch = @ \union produce]

(* These operators are only called on nodes which are executable in the context
   of the specific current transaction.
   That is, we do not have to check for markings anymore, or whether a
   condition of an intermediate event is fulfilled. *)

executeTask(n) ==
  /\ modifyMarking({ incoming(n) } \union { incoming(nn) : nn \in siblings[n] }, { outgoing(n) })

executeEventEnd(n) ==
  /\ modifyMarking({ incoming(n) }, {})

executeEventIntermediate(n) ==
  /\ modifyMarking({ incoming(n) } \union { incoming(nn) : nn \in siblings[n] }, { outgoing(n) })

executeGatewayEvent(n) ==
  /\ modifyMarking({ incoming(n) }, { f \in Flows : source[f] = n })

executeGatewayParallel(n) ==
  /\ modifyMarking({ f \in Flows : target[f] = n }, { f \in Flows : source[f] = n })

executeGatewayExclusive(n) ==
  /\ LET enabledFlows == { f \in Flows : source[f] = n /\ evaluateFlow(f, oracleValues, messageValues) } IN
    IF enabledFlows /= {} THEN
      /\ \E f \in enabledFlows :
        /\ modifyMarking({ ff \in Flows : target[ff] = n }, { f })
    ELSE
      /\ modifyMarking({ f \in Flows : target[f] = n }, { defaultFlow[n] })

(* ---------------------- *)
(* ---   Enablement   --- *)
(* ---------------------- *)
hasToken(f) == \E m \in marking : m[1] = f

triggerTimeAfter(n, t) ==
  CASE nodeType[n] = EventIntermediate ->
        LET triggerTimes == { tt \in t..timestamp : evaluateEventAt(n, t, tt, marking, oracleValues, messageValues) } IN
          IF triggerTimes = {}
          THEN PAST
          ELSE CHOOSE tt \in triggerTimes : \A ttt \in triggerTimes : tt <= ttt
    [] nodeType[n] = Task -> timestamp + 1
    [] OTHER -> FALSE

isExecutionFlow(n, f) ==
  /\ \E m \in marking :
    /\ m[1] = f
    /\ target[m[1]] = n
    /\ CASE nodeType[n] = GatewayParallel -> \A ff \in Flows : target[ff] = n => hasToken(ff)
         [] nodeType[n] \in { Task, EventIntermediate } -> LET t == triggerTimeAfter(n, m[2]) IN
            /\ PAST < t
            /\ ~\E nn \in siblings[n] : LET tt == triggerTimeAfter(nn, m[2]) IN
              /\ PAST < tt
              /\ tt < t
         [] OTHER -> TRUE

executionFlows(n) == { f \in Flows : isExecutionFlow(n, f) }

executeNode(n) ==
  /\ UNCHANGED <<oracleValues, messageValues>>
  /\ CASE nodeType[n] = Task -> executeTask(n)
       [] nodeType[n] = GatewayParallel -> executeGatewayParallel(n)
       [] nodeType[n] = GatewayExclusive -> executeGatewayExclusive(n)
       [] nodeType[n] = GatewayEvent -> executeGatewayEvent(n)
       [] nodeType[n] = EventEnd -> executeEventEnd(n)
       [] nodeType[n] = EventIntermediate -> executeEventIntermediate(n)
       [] OTHER -> FALSE

executableNodes == { n \in Nodes :
  /\ nodeType[n] = Task => curTx.target = n
  /\ \E f \in executionFlows(n) : f \in curTx.touch
}

(* ---------------------- *)
(* ---     Tasks      --- *)
(* ---------------------- *)
doStartTaskTx(t, f) ==
  /\ \E mv \in MessageDomain[t] :
    /\ curTx' = [ type |-> TaskTx,
                  target |-> t,
                  payload |-> mv,
                  touch |-> { f } ]
    /\ messageValues' = [ messageValues EXCEPT ![t] = mv ]

startTaskTx ==
  /\ UNCHANGED <<oracleValues, timestamp, marking>>
  /\ \E n \in Tasks :
    (* Direct Enablement.
      A task is directly enabled, if there is a token on any incoming sequence flow.
      Structure: _fi_ (t) *)
    \/
      /\ executionFlows(n) /= {}
      /\ doStartTaskTx(n, incoming(n))

    (* Event Enablement.
      A task is event enabled, if it comes after an event that has or would have been able
      to fire at some point in the past, taking into account deferred choice situations. *)
    \/
      /\ nodeType[predecessor(n)] = EventIntermediate
      /\ executionFlows(predecessor(n)) /= { }
      /\ doStartTaskTx(n, incoming(predecessor(n)))

startOracleTx ==
  \E o \in Oracles :
    /\ oracleValues[o][2] < timestamp \* only allow one change per timestep
    /\ \E v \in OracleDomain[o] :
      /\ oracleValues' = [ oracleValues EXCEPT ![o] = <<v, timestamp>> ]
      /\ curTx' = [ type |-> OracleTx,
                    target |-> o,
                    payload |-> v,
                    touch |-> {} ]
  /\ UNCHANGED <<marking, messageValues, timestamp>>

(* ---------------------- *)
(* ---    Timestep    --- *)
(* ---------------------- *)
timestep ==
  /\ timestamp < MAX_TIMESTAMP
  /\ UNCHANGED <<marking, oracleValues, messageValues>>
  /\ curTx' = [ type |-> NoTx,
                target |-> Empty,
                payload |-> NoPayload,
                touch |-> {} ]
  /\ timestamp' = timestamp + 1

(* ---------------------- *)
(* ---  Transactions  --- *)
(* ---------------------- *)
canStartNewTx ==
  CASE curTx.type = TaskTx -> executableNodes = {}
    [] curTx.type = DeployTx -> executableNodes = {}
    [] curTx.type = OracleTx -> TRUE
    [] curTx.type = NoTx -> TRUE

processTaskTx ==
  /\ curTx.type = TaskTx
  /\ UNCHANGED timestamp
  /\ \E n \in executableNodes : executeNode(n)

processOracleTx ==
  /\ curTx.type = OracleTx
  /\ PUSH_ORACLES \* TODO Update PUSH_ORACLES
  /\ UNCHANGED timestamp
  /\ \E n \in executableNodes : executeNode(n)

processDeployTx ==
  /\ curTx.type = DeployTx
  /\ UNCHANGED timestamp
  /\ \E n \in executableNodes : executeNode(n)

hasFinished == marking = {}

(* ---------------------- *)
(* ---  Transitions   --- *)
(* ---------------------- *)
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
  /\ curTx = [ type |-> DeployTx,
               target |-> Empty,
               payload |-> NoPayload,
               touch |-> { f \in Flows : nodeType[source[f]] = EventStart } ]

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
  /\ oracleValues \in [ Oracles -> AllOracleDomains \X (Nat \union { PAST }) ]
  /\ \A o \in Oracles : oracleValues[o][1] \in OracleDomain[o]
  /\ messageValues \in [ Tasks -> AllMessageDomains ]
  /\ \A t \in Tasks : messageValues[t] \in { NoPayload } \union MessageDomain[t]
  /\ timestamp \in 0..MAX_TIMESTAMP
  /\ curTx \in [ type : TxType,
                 target : (Tasks \union Oracles \union { Empty }),
                 payload : PayloadDomain,
                 touch : SUBSET Flows ]

================================================================
