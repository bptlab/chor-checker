---------------- MODULE Semantics ----------------

EXTENDS TLC, FiniteSets, Sequences, Integers, Naturals, Types

VARIABLES marking
var == <<marking>>

(*
- one incoming and one outgoing sequence flow, except for gateways
- 1-safe
*)

\* local vs global propagation, sync vs async events

(*
Async events can be "fired" in a new transaction if there is a token in front of them, simulating a query
*)

LOCAL INSTANCE Choreography

RECURSIVE MegaCartesianProduct(_)
MegaCartesianProduct(SetOfSetsOfMarkings) ==
  IF (Cardinality(SetOfSetsOfMarkings) = 0) THEN {{}}
  ELSE IF (Cardinality(SetOfSetsOfMarkings) = 1) THEN CHOOSE X \in SetOfSetsOfMarkings : TRUE
  ELSE
    LET A == CHOOSE X \in SetOfSetsOfMarkings : TRUE
        B == CHOOSE X \in SetOfSetsOfMarkings : X /= A IN
      MegaCartesianProduct(
        (SetOfSetsOfMarkings \ { A, B }) \union {{
          M1 \union M2 : <<M1, M2>> \in A \X B
        }}
      )

(* There should always be exactly one incoming and outgoing sequence flow.
   These operators should not be called on nodes where this is not guaranteed. *)
\* incoming(n) == CHOOSE f \in Flows : target[f] = n
outgoing(n) == CHOOSE f \in Flows : source[f] = n

Incoming(n) == { f \in Flows : target[f] = n }
Outgoing(n) == { f \in Flows : source[f] = n }

\* successor(n) == target[outgoing(n)]
\* predecessor(n) == source[incoming(n)]

Successors(n) == { m \in Nodes : \E f \in Flows : source[f] = n /\ target[f] = m }
Predecessors(n) == { m \in Nodes : \E f \in Flows : source[f] = m /\ target[f] = n }

Siblings[n \in Nodes] == (UNION { Successors(nn) : nn \in { nnn \in Predecessors(n) : nodeType[nnn] = EventBasedGateway } } ) \ { n }

isEnabled(M, n) ==
  \/ n \in M
  \/ \E f \in Incoming(n) : f \in M

RECURSIVE FlipMarkings(_, _)
FlipMarkings(M, f) == LET n == target[f] IN
  IF nodeType[n] = BlockingTask THEN {{ n }}
  ELSE IF nodeType[n] = NonBlockingTask THEN FlipMarkings(M, outgoing(n))
  ELSE IF nodeType[n] = ExclusiveGateway THEN UNION { FlipMarkings(M, ff) : ff \in Outgoing(n) }
  ELSE IF nodeType[n] = ParallelGateway THEN (
    IF \E ff \in Flows: (ff /= f /\ target[ff] = n /\ ff \notin M)
    THEN {{ f }} \* block if not all tokens are there
    (* All different combinations of outcomes when propagating on all outgoing arcs, plus consume incoming *)
    ELSE { X \union (Incoming(n) \ {f}) : X \in MegaCartesianProduct({ FlipMarkings(M, ff) : ff \in Outgoing(n) }) }
  )
  ELSE IF nodeType[n] = EventBasedGateway THEN (
    LET OutgoingSync(nn) == { ff \in Outgoing(nn) : nodeType[target[ff]] = IntermediateCatchEvent /\ isSync[target[ff]] } IN
      { Outgoing(n) } \* enable all outgoing events and stop
      \union
      UNION { FlipMarkings(M, ff) : ff \in OutgoingSync(n) } \* pass through one of the sync events
  )
  ELSE IF nodeType[n] = EndEvent THEN {{}}
  ELSE IF nodeType[n] = IntermediateCatchEvent THEN (
    IF isSync[n]
    THEN {{ f }} \union FlipMarkings(M, outgoing(n))
    ELSE {{ f }} \* Async needs a transaction with itself as the target, e.g., a callback
  )
  ELSE FlipMarkings(M, outgoing(n)) \* REGULAR

SymmetricDifference(A, B) ==
  { x \in (A \union B) : x \notin A \/ x \notin B}

RECURSIVE triggerNodes(_, _)
triggerNodes(N, M) ==
  IF Cardinality(N) = 0 THEN {{}}
  ELSE
    LET
      n == CHOOSE nn \in N : TRUE
      Consume ==
        IF nodeType[n] \in TaskType
        THEN { n }
        ELSE Incoming(n) \union UNION { Incoming(nn) : nn \in Siblings[n] }
    IN
      IF Cardinality(N) = 1 THEN { F \union Consume : F \in FlipMarkings(M, outgoing(n)) }
      ELSE
        LET
          RecursiveFlips == triggerNodes(N \ { n }, M)
          ThisFlips(F) == FlipMarkings(SymmetricDifference(M, F), outgoing(n))
        IN
          UNION { { SymmetricDifference(MM, F) \union Consume : MM \in ThisFlips(F) } : F \in RecursiveFlips }

transaction ==
  \E n \in Nodes :
    /\ isEnabled(marking, n)
    /\ \E F \in triggerNodes({ n }, marking) : marking' = SymmetricDifference(marking, F)

Next ==
  /\ marking /= {}
  /\ transaction

Init ==
  /\ marking \in triggerNodes({ n \in Nodes : nodeType[n] = StartEvent }, {})

Fairness ==
  /\ WF_var(transaction)

Spec == Init /\ [][Next]_var /\ Fairness

TypeInvariant ==
  /\ marking \subseteq Flows \union Tasks

================================================================
