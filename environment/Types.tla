---------------- MODULE Types ----------------

(* choreography types *)
Task == "Task"
GatewayExclusive == "GatewayExclusive"
GatewayParallel == "GatewayParallel"
GatewayEvent == "GatewayEvent"
EventStart == "EventStart"
EventEnd == "EventEnd"
EventIntermediate == "EventIntermediate"

FlowNormal == "FlowNormal"
FlowConditional == "FlowConditional"
FlowDefault == "FlowDefault"

GatewayType == { GatewayExclusive, GatewayParallel, GatewayEvent }
EventType == { EventStart, EventIntermediate, EventEnd }
FlowType == { FlowNormal, FlowConditional, FlowDefault }

NodeType == { Task } \union GatewayType \union EventType

Empty == "-"
NoPayload == 0

(* transaction types *)
TaskTx == "TaskTx"
OracleTx == "OracleTx"

TxType == { Empty, TaskTx, OracleTx }

================================================================
