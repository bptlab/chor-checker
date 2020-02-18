---------------- MODULE Semantics ----------------

EXTENDS Naturals, Types, Definitions, FiniteSets

(* runtime *)
VARIABLES
  marking

var == <<marking>>

TypeInvariant == marking \in [ Flows -> Nat ]


taskIsEnabled(n) ==
  /\ nodeType[n] = Task
  /\ \E f \in incoming(n) : marking[f] >= 1

task(n) ==
  /\ taskIsEnabled(n)
  /\ \E fi \in incoming(n) :
       /\ marking[fi] >= 1
       /\ marking' = [ f \in DOMAIN marking |->
                           IF f = fi THEN marking[f] - 1
                           ELSE IF f \in outgoing(n) THEN marking[f] + 1
                           ELSE marking[f] ]

gatewayParallel(n) ==
  /\ nodeType[n] = GatewayParallel
  /\ \A f \in incoming(n) : marking[f] >= 1
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN marking[f] - 1
                      ELSE IF f \in outgoing(n) THEN marking[f] + 1
                      ELSE marking[f] ]

eventEnd(n) ==
  /\ nodeType[n] = EventEnd
  /\ \E f \in incoming(n) : marking[f] >= 1
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN 0
                      ELSE marking[f] ]


step(n) == CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
             [] nodeType[n] = Task -> task(n)
             [] nodeType[n] = EventEnd -> eventEnd(n)
             [] OTHER -> FALSE \* start events

Next == \E n \in Nodes : step(n)

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN 1
                     ELSE 0 ]

Spec == Init /\ [][Next]_var




\*NoTokensLeft ==
\*  \A f \in Flows : <>(\E n \in ContainRel[p] :  marking[n] = 0)

Safety ==
  [](\A f \in Flows : marking[f] <= 1)

================================================================
