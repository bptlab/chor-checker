---------------- MODULE SemanticsContinual ----------------

EXTENDS TLC, FiniteSets, Sequences, Integers, Naturals, Types

VARIABLES tx, time, marking, age, detections, requests
var == <<tx, time, marking, age, detections, requests>>

LOCAL INSTANCE Choreography

NIL == "Nil"
FUTURE == 100000

ExternalEvents == { n \in Nodes : nodeType[n] \in EventExternalType }
ImplicitExternalEvents == { n \in Nodes : nodeType[n] \in EventImplicitExternalType }

(*
- Tx: target, global

- Each event has a detection timestamp:
  * 0 not yet probed or currently being probed (async oracle)
  * \top has not happened yet
  * anything else: first detected at that point in time

- Gateway is first reached:
  * Set all message events to \top
  * Detect timer events
  * Sync oracle: detect conditional event
  * Async oracle: set to 0, issue ORACLE REQUEST
  -> IF ALL EVENTS i > 0: trigger lowest timestamp if possible
- Oracle callback for ORACLE REQUEST:
  * Set to time stored in ORACLE REQUEST *or* set to \top
  -> IF ALL EVENTS i > 0: trigger lowest timestamp if possible
- Unbound message event i transaction:
  * ALL DETECTIONS ARE \top
  * Set message event i detection to curtime
  * Detect timer events
  * Sync oracle: detect conditional event
  * Async oracle: set to 0, issue ORACLE REUEST
  -> IF ALL EVENTS i > 0: trigger lowest timestamp if possible

These re-evaluation transactions are on top of regular transactions
- Re-evaluate gateway, if all are \top:
  * Same as when first reached
  -> IF ALL EVENTS i > 0: trigger one of them
*)

incoming(n) == CHOOSE f \in Flows : target[f] = n
outgoing(n) == CHOOSE f \in Flows : source[f] = n

predecessor(n) == source[incoming(n)]

Incoming(n) == { f \in Flows : target[f] = n }
Outgoing(n) == { f \in Flows : source[f] = n }

Successors(n) == { m \in Nodes : \E f \in Flows : source[f] = n /\ target[f] = m }
Predecessors(n) == { m \in Nodes : \E f \in Flows : source[f] = m /\ target[f] = n }




changeMarking(Consume, Produce) ==
  /\ marking' = (marking \ Consume) \union Produce
  /\ age' = [ f \in marking' |-> IF f \in marking THEN age[f] ELSE time ]


executeExclusiveGateway(n) ==
  /\ UNCHANGED detections, requests
  /\ \E fi \in Incoming(n) :
    /\ fi \in marking
    /\ \E fo \in Outgoing(n) : changeMarking({ fi }, { fo })

executeParallelGateway(n) ==
  /\ UNCHANGED detections, requests
  /\ Incoming(n) \ marking = {}
  /\ changeMarking(Incoming(n), Outgoing(n))

executeScriptTask(n) ==
  /\ UNCHANGED detections, requests
  /\ incoming(n) \in marking
  /\ changeMarking({ incoming(n) }, { outgoing(n) })

executeSendTask(n) == \* Does this work if there is no message flow target?
  LET nn == messageFlowTarget[n] IN
  /\ UNCHANGED detections, requests
  /\ incoming(n) \in marking
  /\ IF mm /= NIL THEN
      /\ incoming(nn) \in marking
      /\ changeMarking({ incoming(n), incoming(nn) }, { outgoing(n), outgoing(nn) })
     ELSE changeMarking({ incoming(n) }, {outgoing(n)})

executeEndEvent(n) ==
  /\ UNCHANGED detections, requests
  /\ incoming(n) \in marking
  /\ changeMarking({ incoming(n) }, {})



isInternalReceiveEvent(n) ==
  /\ nodeType[n] = EventReceive
  /\ \E nn \in Nodes :
    /\ nodeType[nn] = TaskSend
    /\ nn \in DOMAIN messageFlowTarget
    /\ messageFlowTarget[nn] = n


canFire(n) ==
  /\ nodeType[n] \in ExternalEvents
  /\ detections[n] > 0
  /\ detections[n] < FUTURE
  /\ \* No sibling can fire earlier, and all are evaluated
  /\ nodeType[n] = EventReceive => tx.target = n


executeDeferredGateway(n) == FALSE
  \* TODO

executeTimerEvent(n) ==
  /\ UNCHANGED detections, requests
  /\ canFire(n)
  /\ incoming(n) \in marking
  /\ changeMarking(SiblingFlows(n), { outgoing(n) })

executeConditionalEvent(n) ==
  /\ UNCHANGED detections, requests
  /\ canFire(n)
  /\ incoming(n) \in marking
  /\ changeMarking(SiblingFlows(n), { outgoing(n) })

executeIntermediateEvent(n) ==
  \* Only timer, sync conditional
  \* For async conditional, send request



enterReceiveEvent(n) ==
  /\ UNCHANGED time, detections, requests
  /\ ~isInternalReceiveEvent(n)
  /\ tx' = [ target |-> n, global |-> TRUE ]
  /\ incoming(n) \in marking \* check deferred choice
  /\ changeMarking({ incoming(n) }, { outgoing(n) })

enterTimerEvent(n) ==
  /\ UNCHANGED time, detections, requests
  /\ detect(n, age[incoming[n]], time)
  /\ tx' = [ target |-> n, global |-> TRUE ]
  /\ incoming(n) \in marking \* check deferred choice
  /\ changeMarking({ incoming(n) }, { outgoing(n) })

enterConditionalEvent(n) ==
  /\ detect(n, age[incoming[n]], time)
  /\ tx' = [ target |-> n, global |-> TRUE ]
  /\ incoming(n) \in marking \* check deferred choice
  /\ changeMarking({ incoming(n) }, { outgoing(n) })

enterUserTask(n) ==

enterOracleCallback(r) ==

startTransaction ==
  /\ tx = NIL
  /\
    \/ \E n \in Nodes :
      CASE nodeType[n] = EventReceive -> enterReceiveEvent(n)
        [] nodeType[n] = EventTimer -> enterTimerEvent(n)
        [] nodeType[n] = EventConditional -> enterConditionalEvent(n)
        [] nodeType[n] = TaskUser -> enterUserTask(n)
        OTHER -> FALSE
    \/ \E r \in requests : enterOracleCallback(r)

performAsyncEventRequests(n) ==
  /\ tx /= NIL
  /\ UNCHANGED tx, time, marking, age, detections
  /\ \E n \in ExternalEvents :
    /\ incoming(n) \in marking
    /\ detections[n] = 0
    /\ ~isSync[n]
    /\ \A r \in requests : r[1] /= n
    /\ requests' = requests \union { <<n, time>> }

performSyncEventDetection(n) ==
  /\ tx /= NIL
  /\ UNCHANGED tx, time, marking, age, requests
  /\ \E n \in ExternalEvents :
    /\ incoming(n) \in marking
    /\ detections[n] = 0
    /\ isSync[n]
    /\ IF detect(n, age[incoming[n]], time)
       THEN detections' = [ detections EXCEPT ![n] = time ]
       ELSE detections' = [ detections EXCEPT ![n] = FUTURE ]

executeNode(n) ==
  /\ tx /= NIL
  /\ UNCHANGED tx, time
  /\ \E n \in nodes :
      CASE nodeType[n] = GatewayExclusive -> executeExclusiveGateway(n)
        [] nodeType[n] = GatewayParallel -> executeParallelGateway(n)
        [] nodeType[n] = GatewayDeferred -> executeDeferredGateway(n)
        [] nodeType[n] = TaskScript -> executeScriptTask(n)
        [] nodeType[n] = TaskSend -> executeSendTask(n)
        [] nodeType[n] = EventMessage -> executeMessageEvent(n)
        [] nodeType[n] = EventTimer -> executeTimerEvent(n)
        [] nodeType[n] = EventConditional -> executeConditionalEvent(n)
        [] nodeType[n] = EventEnd -> executeEndEvent(n)

  \*       /\ marking' = (marking \ Consume) \union Produce
  \* /\ age' = [ f \in marking' |-> IF f \in marking THEN age[f] ELSE time ]
\*   /\ IF nodeType[n] = TaskUser THEN time' = time + 1 ELSE 

progressTransaction ==
  \/ \E n \in Nodes : executeNode(n)
  \/ \E n \in ExternalEvents : performSyncEventDetection(n)
  \/ \E n \in ExternalEvents : performAsyncEventRequest(n)

Next ==
  /\ marking /= {}
  /\
    \/ progressTransaction
    \/ endTransaction
    \/ startTransaction
    \/ timestep

Init ==
  /\ marking = UNION { Outgoing(n) : n \in { nn \in Nodes : nodeType[nn] = EventStart } }
  /\ time = 0
  /\ age = [ f \in marking |-> time ]
  /\ tx = <<NIL, TRUE>>
  /\ detections = [ f \in ExternalEvents |-> 0 ]
  /\ requests = {}

Fairness ==
  /\ WF_var(execute)

Spec == Init /\ [][Next]_var /\ Fairness

TypeInvariant ==
  /\ marking \subseteq Flows
  /\ time \in Nat
  /\ time < 100
  /\ age \in [ f \in marking -> Nat ]
  /\
    \/ tx = NIL
    \/ tx \in [ target: Nodes \union { NIL }, global: {TRUE, FALSE} ]
  /\ detections \in [ f \in ExternalEvents -> Nat ]
  /\ requests \subseteq ExternalEvents \X Nat

\* ConsumeSets(n) ==
\*   CASE nodeType[n] = GateParallel -> { Incoming(n) }
\*     [] nodeType[n] = TaskSend /\ n \in DOMAIN messageFlowTarget -> { { incoming(n), incoming(messageFlowTarget[n]) } }
\*     [] nodeType[n] \in EventExternalType /\ nodeType[predecessor(n)] = GateDeferred -> { Outgoing(predecessor(n)) }
\*     [] OTHER -> { { f } : f \in Incoming(n) }

\* ProduceSets(n) ==
\*   CASE nodeType[n] = GateExclusive -> { { f } : f \in Outgoing(n) }
\*     [] nodeType[n] = TaskSend ->
\*           IF n \in DOMAIN messageFlowTarget
\*           THEN { Outgoing(n) \union Outgoing(messageFlowTarget[n]) }
\*           ELSE { Outgoing(n) }
\*     [] OTHER -> { Outgoing(n) }

\* timestep ==
\*   /\ UNCHANGED <<marking, age>>
\*   /\ time' = time + 1
\*   /\ \A n \in Nodes :
\*     \/ ~isEnabled(n)
\*     \/ \A Consume \in ConsumeSets(n) : Consume \ marking /= {}

================================================================
