---------------- MODULE Choreography ----------------

EXTENDS TLC, Naturals, Types

VARIABLES marking, timestamp, oracleValues, messageValues, curTx

Nodes == {
  "X", "Y", "Z", "W",
  "E1", "E2", "EC", "ET",
  "G1", "G2"
}
Flows == {
  "F1", "F2", "F3", "F3.2", "F3.3", "F4", "F5", "F6", "F7", "F8"
}

source ==
   "F1" :> "E1"
@@ "F2" :> "X"
@@ "F3" :> "G1"
@@ "F3.2" :> "EC"
@@ "F3.3" :> "ET"
@@ "F4" :> "G1"
@@ "F5" :> "Y"
@@ "F6" :> "Z"
@@ "F7" :> "G2"
@@ "F8" :> "W"

target ==
   "F1" :> "X"
@@ "F2" :> "G1"
@@ "F3" :> "EC"
@@ "F3.2" :> "ET"
@@ "F3.3" :> "Y"
@@ "F4" :> "Z"
@@ "F5" :> "G2"
@@ "F6" :> "G2"
@@ "F7" :> "W"
@@ "F8" :> "E2"

nodeType ==
   "X" :> Task
@@ "Y" :> Task
@@ "Z" :> Task
@@ "W" :> Task
@@ "E1" :> EventStart
@@ "E2" :> EventEnd
@@ "EC" :> EventConditional
@@ "ET" :> EventTimer
@@ "G1" :> GatewayExclusive
@@ "G2" :> GatewayExclusive

defaultFlow ==
   "G1" :> "F3"
@@ "G2" :> "F7"

Oracles == {
  "EURUSD",
  "WEATHER"
}
OracleDomain ==
   "EURUSD" :> { 1, 2, 3 }
@@ "WEATHER" :> { 8, 9, 10 }
AllOracleDomains == UNION { OracleDomain[o] : o \in DOMAIN OracleDomain }

MessageDomain == { 100 }

PayloadDomain == { NoPayload } \union MessageDomain \union AllOracleDomains

(* For these conditions, we can not use the variables directly. We have
   to get them as parameters. TODO Think of a better naming. *)
evaluateIntermediateEvent(n, f, ma, ti, or, me) ==
  \/ n = "ET" => ti - ma[f][2] = 2
  \/ n = "EC" => or["WEATHER"] = 9

evaluateFlow(f, or, me) ==
  CASE f = "F4" -> or["WEATHER"] = 8
    [] OTHER -> FALSE

INSTANCE Semantics

================================================================
