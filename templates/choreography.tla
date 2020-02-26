---------------- MODULE Choreography ----------------

EXTENDS TLC, Naturals, Types

(* Oracles, data, bindings, ... *)

VARIABLES marking, awaitTransaction, aging, timestamp, oracleValues, messageValues

Nodes == {
  "X", "Y", "Z", "W",
  "E1", "E2",
  "G1", "G2"
}
Flows == { "F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8" }
Oracles == {
  "EURUSD"
}

source ==
   "F1" :> "E1"
@@ "F2" :> "X"
@@ "F3" :> "G1"
@@ "F4" :> "G1"
@@ "F5" :> "Y"
@@ "F6" :> "Z"
@@ "F7" :> "G2"
@@ "F8" :> "W"

target ==
   "F1" :> "X"
@@ "F2" :> "G1"
@@ "F3" :> "Y"
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
@@ "G1" :> GatewayParallel
@@ "G2" :> GatewayParallel

Tasks == { n \in Nodes : nodeType[n] = Task }

INSTANCE Semantics

================================================================
