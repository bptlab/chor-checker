---------------- MODULE Types ----------------

(* choreography types *)
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

(* transaction types *)
NoTx == "NoTx"
ChoreoTx == "ChoreoTx"
OracleTx == "OracleTx"

TxType == { NoTx, ChoreoTx, OracleTx }

NoPayload == 0

================================================================
