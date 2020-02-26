---------------- MODULE Semantics ----------------

EXTENDS TLC, Types, Definitions, FiniteSets

(* runtime *)
VARIABLES marking, awaitTransaction

var == <<marking, awaitTransaction>>

TypeInvariant == marking \in [ Flows -> BOOLEAN ]
  /\ awaitTransaction \in BOOLEAN

taskIsEnabled(n) ==
  /\ nodeType[n] = Task
  /\ \E f \in incoming(n) : marking[f]

task(n) ==
  /\ taskIsEnabled(n)
  /\ \E fi \in incoming(n) :
       /\ marking[fi]
       /\ marking' = [ f \in DOMAIN marking |->
                           IF f = fi THEN FALSE
                           ELSE IF f \in outgoing(n) THEN TRUE
                           ELSE marking[f] ]

oracle(o) == TRUE

gatewayParallel(n) ==
  /\ nodeType[n] = GatewayParallel
  /\ \A f \in incoming(n) : marking[f]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN FALSE
                      ELSE IF f \in outgoing(n) THEN TRUE
                      ELSE marking[f] ]

eventEnd(n) ==
  /\ nodeType[n] = EventEnd
  /\ \E f \in incoming(n) : marking[f]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN FALSE
                      ELSE marking[f] ]

stepInternal(n) == 
  CASE nodeType[n] = GatewayParallel -> gatewayParallel(n) /\ awaitTransaction' = FALSE
    [] nodeType[n] = EventEnd -> eventEnd(n) /\ awaitTransaction' = FALSE
    [] OTHER ->
      /\ awaitTransaction' = TRUE
      /\ UNCHANGED <<marking>>

stepTransaction(n) ==
  CASE nodeType[n] = Task ->
      /\ task(n)
      /\ awaitTransaction' = FALSE
    [] OTHER -> FALSE

Next == \E n \in Nodes :
  /\ awaitTransaction => stepTransaction(n)
  /\ ~awaitTransaction => stepInternal(n)

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN TRUE
                     ELSE FALSE ]
  /\ awaitTransaction = TRUE

Spec == Init /\ [][Next]_var

\*NoTokensLeft ==
\*  \A f \in Flows : <>(\E n \in ContainRel[p] :  marking[n] = 0)

Safety ==
  [](\E f \in Flows : marking[f])

================================================================
