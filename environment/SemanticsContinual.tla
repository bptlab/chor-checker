---------------- MODULE SemanticsContinual ----------------

EXTENDS TLC, FiniteSets, Sequences, Integers, Naturals, Types

VARIABLES time, marking, age
var == <<time, marking, age>>

LOCAL INSTANCE Choreography

incoming(n) == CHOOSE f \in Flows : target[f] = n
outgoing(n) == CHOOSE f \in Flows : source[f] = n

predecessor(n) == source[incoming(n)]

Incoming(n) == { f \in Flows : target[f] = n }
Outgoing(n) == { f \in Flows : source[f] = n }

Successors(n) == { m \in Nodes : \E f \in Flows : source[f] = n /\ target[f] = m }
Predecessors(n) == { m \in Nodes : \E f \in Flows : source[f] = m /\ target[f] = n }

Siblings[n \in Nodes] == (UNION { Successors(nn) : nn \in { nnn \in Predecessors(n) : nodeType[nnn] = GateDeferred } } ) \ { n }

isConnectedReceiveEvent(n) ==
  /\ nodeType[n] = EventReceive
  /\ \E nn \in Nodes :
    /\ nodeType[nn] = TaskSend
    /\ messageFlowTarget[nn] = n

isEnabled(n) == nodeType[n] \in EventExternalType => IF incoming(n) \in marking /\ ~isConnectedReceiveEvent(n) THEN detect(n, age[incoming(n)], time) ELSE FALSE

ConsumeSets(n) ==
  CASE nodeType[n] = GateParallel -> { Incoming(n) }
    [] nodeType[n] = TaskSend /\ n \in DOMAIN messageFlowTarget -> { { incoming(n), incoming(messageFlowTarget[n]) } }
    [] nodeType[n] \in EventExternalType /\ nodeType[predecessor(n)] = GateDeferred -> { Outgoing(predecessor(n)) }
    [] OTHER -> { { f } : f \in Incoming(n) }

ProduceSets(n) ==
  CASE nodeType[n] = GateExclusive -> { { f } : f \in Outgoing(n) }
    [] nodeType[n] = TaskSend ->
          IF n \in DOMAIN messageFlowTarget
          THEN { Outgoing(n) \union Outgoing(messageFlowTarget[n]) }
          ELSE { Outgoing(n) }
    [] OTHER -> { Outgoing(n) }

timestep ==
  /\ UNCHANGED <<marking, age>>
  /\ time' = time + 1
  /\ \A n \in Nodes :
    \/ ~isEnabled(n)
    \/ \A Consume \in ConsumeSets(n) : Consume \ marking /= {}

executeNode(n) ==
  /\ UNCHANGED time
  /\ isEnabled(n)
  /\ \E Consume \in ConsumeSets(n) :
    /\ Consume \ marking = {}
    /\ \E Produce \in ProduceSets(n) :
      /\ \E f \in Incoming(n) :
        /\ f \in marking
        /\ marking' = (marking \ Consume) \union Produce
  /\ age' = [ f \in marking' |-> IF f \in marking THEN age[f] ELSE time ]
\*   /\ IF nodeType[n] = TaskUser THEN time' = time + 1 ELSE 

execute ==
  \E n \in Nodes : executeNode(n)

Next ==
  /\ marking /= {}
  /\
    \/ execute
    \/ timestep

Init ==
  /\ marking = UNION { Outgoing(n) : n \in { nn \in Nodes : nodeType[nn] = EventStart } }
  /\ time = 0
  /\ age = [ f \in marking |-> time ]

Fairness ==
  /\ WF_var(execute)

Spec == Init /\ [][Next]_var /\ Fairness

TypeInvariant ==
  /\ marking \subseteq Flows
  /\ time \in Nat
  /\ time < 100
  \* /\ age = [ f \in marking |-> Nat ]

================================================================
