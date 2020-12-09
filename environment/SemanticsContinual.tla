---------------- MODULE SemanticsContinual ----------------

EXTENDS TLC, FiniteSets, Sequences, Integers, Naturals, Types

VARIABLES time, marking, age
var == <<time, marking, age>>

LOCAL INSTANCE Choreography

incoming(n) == CHOOSE f \in Flows : target[f] = n
outgoing(n) == CHOOSE f \in Flows : source[f] = n

Incoming(n) == { f \in Flows : target[f] = n }
Outgoing(n) == { f \in Flows : source[f] = n }

Successors(n) == { m \in Nodes : \E f \in Flows : source[f] = n /\ target[f] = m }
Predecessors(n) == { m \in Nodes : \E f \in Flows : source[f] = m /\ target[f] = n }

Siblings[n \in Nodes] == (UNION { Successors(nn) : nn \in { nnn \in Predecessors(n) : nodeType[nnn] = GateDeferred } } ) \ { n }

detect(n, ta, tc) ==
  CASE nodeType[n] = EventTimer -> ta + 2 < tc
    [] OTHER -> FALSE


isEnabled(n) ==
  CASE nodeType[n] = GateParallel -> \A f \in Incoming(n) : f \in marking
    [] nodeType[n] = TaskSend ->
          /\ \E f \in Incoming(n) : f \in marking
          /\ n \in DOMAIN messageFlowTarget => \E f \in Incoming(messageFlowTarget[n]) : f \in marking
    [] nodeType[n] \in EventType -> \E f \in Incoming(n) :
                                      /\ f \in marking
                                      /\ detect(n, age[f], time)
    [] OTHER -> \E f \in Incoming(n) : f \in marking

Consume(n, f) ==
  CASE nodeType[n] = GateParallel -> Incoming(n)
    [] nodeType[n] = TaskSend ->
          IF n \in DOMAIN messageFlowTarget
          THEN { f } \union Incoming(messageFlowTarget[n])
          ELSE { f }
    [] nodeType[n] \in EventType \ { EventNone } ->
         IF nodeType[source[f]] = GateDeferred
         THEN Outgoing(source[f])
         ELSE { f }
    [] OTHER -> { f }

ProduceVariants(n) ==
  CASE nodeType[n] = GateExclusive -> { { f } : f \in Outgoing(n) }
    [] nodeType[n] = TaskSend ->
          IF n \in DOMAIN messageFlowTarget
          THEN { Outgoing(n) \union Outgoing(messageFlowTarget[n]) }
          ELSE { Outgoing(n) }
    [] OTHER -> { Outgoing(n) }

timestep ==
  /\ UNCHANGED <<marking, age>>
  /\ time' = time + 1
  /\ \A n \in Nodes : ~isEnabled(n) \* \/ nodeType[n] = TaskUser

executeNode(n) ==
  /\ UNCHANGED time
  /\ isEnabled(n)
  /\ \E ProduceVariant \in ProduceVariants(n) :
    /\ \E f \in Incoming(n) :
      /\ f \in marking
      /\ marking' = (marking \ Consume(n, f)) \union ProduceVariant
\*   /\ IF nodeType[n] = TaskUser THEN time' = time + 1 ELSE 
  /\ age' = [ f \in marking' |-> IF f \in marking THEN age[f] ELSE time ]

execute ==
  \E n \in Nodes : executeNode(n)

Next ==
  /\ marking /= {}
  /\
    \/ execute
    \/ timestep

Init ==
  /\ marking = UNION { Outgoing(n) : n \in { nn \in Nodes : nodeType[nn] = EventNone /\ Incoming(nn) = {} } }
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
