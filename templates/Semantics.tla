---------------- MODULE Semantics ----------------

EXTENDS TLC, Types, Definitions, FiniteSets

(* runtime *)
VARIABLES
  marking

RECURSIVE propagateTokens(_,_)

\* Look into EXCEPT syntax for better markings

var == <<marking>>

TypeInvariant == marking \in [ Flows -> BOOLEAN ]

taskIsEnabled(n) ==
  /\ nodeType[n] = Task
  /\ \E f \in incoming(n) : marking[f]

task(n) ==
  /\ PrintT(n)
  /\ \E f \in incoming(n) :
    /\ marking[f]
    /\ LET newMarking == [ ff \in DOMAIN marking |->
                         IF ff = f THEN FALSE
                         ELSE IF ff \in outgoing(n) THEN TRUE
                         ELSE marking[ff] ] IN
      /\ (\A ff \in outgoing(n) : propagateTokens(newMarking, ff))
      /\ PrintT(<<"new marking",f,newMarking>>)
      /\ marking' = [ ff \in DOMAIN marking |-> newMarking[ff] ]
      /\ PrintT(<<"new marking applied",f,marking'>>)

(*
Call on outgoing sequence flow of the task.
Then, depending on target, do something.
- parallel: if all incoming have tokens, consume them all and propagate further
            otherwise, stop
- event-based: stop
- exclusive: consume, pick one outgoing, propagate
- task: stop
- end event: consume, stop
- intermediate event: stop
*)
propagateTokens(newMarking, f) == LET n == target[f] IN PrintT(<<"starting for",n, newMarking>>) /\ 
  CASE  nodeType[n] = GatewayParallel ->
          /\ PrintT(<<"parallel gateway", n, newMarking>>)
          /\ (\A fi \in incoming(n) : PrintT(<<"check", fi, newMarking[fi]>>) /\ newMarking[fi]) =>
            /\ PrintT(<<"parallel gateway enabled", n, newMarking>>)
            /\ newMarking = [ ff \in DOMAIN marking |->
                            IF ff \in incoming(n) THEN FALSE
                            ELSE IF ff \in outgoing(n) THEN TRUE
                            ELSE newMarking[ff] ]
            /\ \A fo \in outgoing(n) : propagateTokens(newMarking, fo)
            /\ PrintT(<<"parallel gateway after", n, newMarking>>)
    []  nodeType[n] = EventEnd ->
          newMarking = [ ff \in DOMAIN marking |->
                       IF ff = f THEN FALSE ELSE newMarking[ff] ]
    []  OTHER -> TRUE

\* gatewayParallel(n) ==
\*   /\ nodeType[n] = GatewayParallel
\*   /\ \A f \in incoming(n) : marking'[f]
\*   /\ marking' = [ f \in DOMAIN marking |->
\*                       IF f \in incoming(n) THEN FALSE
\*                       ELSE IF f \in outgoing(n) THEN TRUE
\*                       ELSE marking[f] ]

\* eventEnd(n) ==
\*   /\ nodeType[n] = EventEnd
\*   /\ \E f \in incoming(n) : marking[f]
\*   /\ marking' = [ f \in DOMAIN marking |->
\*                       IF f \in incoming(n) THEN FALSE
\*                       ELSE marking[f] ]


\* step(n) == CASE nodeType[n] = GatewayParallel -> gatewayParallel(n)
\*              [] nodeType[n] = Task -> task(n)
\*              [] nodeType[n] = EventEnd -> eventEnd(n)
\*              [] OTHER -> FALSE \* start events

Next == \E n \in Nodes : (nodeType[n] = Task /\ taskIsEnabled(n)) => task(n)

\* Next == \E n \in Nodes : step(n)

Init ==
  /\ marking = [ f \in Flows |->
                     IF nodeType[source[f]] = EventStart THEN TRUE
                     ELSE FALSE ]

Spec == Init /\ [][Next]_var


\*NoTokensLeft ==
\*  \A f \in Flows : <>(\E n \in ContainRel[p] :  marking[n] = 0)

Safety ==
  [](\E f \in Flows : ~marking[f])

================================================================
