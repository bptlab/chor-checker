---------------- MODULE choreo ----------------

EXTENDS TLC, Naturals, FiniteSets

(* types *)
(* move to own file in the long run *)
Task == "Task"
GatewayExclusive == "GatewayExclusive"
GatewayParallel == "GatewayParallel"
GatewayEvent == "GatewayEvent"
EventStart == "EventStart"
EventEnd == "EventEnd"

FlowNormal == "FlowNormal"
FlowConditional == "FlowConditional"
FlowDefault == "FlowDefault"

GatewayType == { GatewayExclusive, GatewayParallel, GatewayEvent }
EventType == { EventStart, EventEnd }
FlowType == { FlowNormal, FlowConditional, FlowDefault }

NodeType == { Task } \union GatewayType \union EventType

(* specification *)
Nodes == {
  "X", "Y", "Z", "W",
  "E1", "E2",
  "G1", "G2"
}
Flows == { "F1", "F2", "F3", "F4", "F5", "F6", "F7", "F8" }

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

nodeTypes ==
   "X" :> Task
@@ "Y" :> Task
@@ "Z" :> Task
@@ "W" :> Task
@@ "E1" :> EventStart
@@ "E2" :> EventEnd
@@ "G1" :> GatewayParallel
@@ "G2" :> GatewayParallel

(* runtime *)
VARIABLES
  marking

var == <<marking>>

TypeInvariant == marking \in [ Flows -> Nat ]

================================================================
