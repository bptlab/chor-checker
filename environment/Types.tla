---------------- MODULE Types ----------------

(* choreography types *)
Task == "Task"
GatewayExclusive == "GatewayExclusive"
GatewayParallel == "GatewayParallel"
GatewayEvent == "GatewayEvent"
EventStart == "EventStart"
EventEnd == "EventEnd"
EventConditional == "EventConditional"
EventTimer == "EventTimer"

FlowNormal == "FlowNormal"
FlowConditional == "FlowConditional"
FlowDefault == "FlowDefault"

EventIntermediateType == { EventConditional, EventTimer }
GatewayType == { GatewayExclusive, GatewayParallel, GatewayEvent }
EventType == { EventStart, EventEnd } \union EventIntermediateType
FlowType == { FlowNormal, FlowConditional, FlowDefault }

NodeType == { Task } \union GatewayType \union EventType

(* transaction types *)
NoTx == "NoTx"
ChoreoTx == "ChoreoTx"
OracleTx == "OracleTx"

TxType == { NoTx, ChoreoTx, OracleTx }

NoPayload == 0

================================================================
