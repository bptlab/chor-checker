---------------- MODULE Semantics ----------------

EXTENDS Types, Definitions, FiniteSets

(* runtime *)
VARIABLES
  marking

var == <<marking>>

TypeInvariant == marking \in [ Flows -> BOOLEAN ]

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

RECURSIVE propagateTokens(_)
propagateTokens(f) ==
  CASE nodeType[target[f]] = GatewayParallel ->
    LET n == target[f] IN
    (\A fi \in incoming(n) : marking'[f]) =>
      /\ marking' = [ ff \in DOMAIN marking |->
                      IF ff \in incoming(n) THEN FALSE
                      ELSE IF ff \in outgoing(n) THEN TRUE
                      ELSE marking'[ff] ]
      /\ \A fo \in outgoing(n) : propagateTokens(fo)

\* gatewayParallel(n) ==
\*   /\ nodeType[n] = GatewayParallel
\*   /\ \A f \in incoming(n) : marking'[f]
\*   /\ marking' = [ f \in DOMAIN marking |->
\*                       IF f \in incoming(n) THEN FALSE
\*                       ELSE IF f \in outgoing(n) THEN TRUE
\*                       ELSE marking[f] ]

eventEnd(n) ==
  /\ nodeType[n] = EventEnd
  /\ \E f \in incoming(n) : marking[f]
  /\ marking' = [ f \in DOMAIN marking |->
                      IF f \in incoming(n) THEN FALSE
                      ELSE marking[f] ]


\* step(n) == CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
\*              [] nodeType[n] = Task -> task(n)
\*              [] nodeType[n] = EventEnd -> eventEnd(n)
\*              [] OTHER -> FALSE \* start events

Next == \E n \in Nodes : step(n)

\* Next == \E n \in Nodes : step(n)

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN 1
                     ELSE 0 ]

Spec == Init /\ [][Next]_var


\*NoTokensLeft ==
\*  \A f \in Flows : <>(\E n \in ContainRel[p] :  marking[n] = 0)

Safety ==
  [](\A f \in Flows : ~marking[f])

================================================================
