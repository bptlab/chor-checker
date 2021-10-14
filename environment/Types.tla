---------------- MODULE Types ----------------

(* Tasks *)
TaskUser == "TaskUser"
TaskSend == "TaskSend"
TaskScript == "TaskScript"
TaskType == { TaskUser, TaskSend, TaskScript }

(* Gateways *)
GateExclusive == "GateExclusive"
GateParallel == "GateParallel"
GateDeferred == "GateDeferred"
GatewayType == { GateExclusive, GateParallel, GateDeferred }

(* Events *)
EventStart == "EventStart"
EventEnd == "EventEnd"
EventReceive == "EventReceive"
EventTimer == "EventTimer"
EventConditional == "EventConditional"
EventImplicitExternalType == { EventTimer, EventConditional }
EventExternalType == { EventReceive } \union EventImplicitExternalType
EventType == { EventStart, EventEnd } \union EventExternalType

NodeType == TaskType \union GatewayType \union EventType

================================================================
