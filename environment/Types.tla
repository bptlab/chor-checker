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
EventNone == "EventNone"
EventReceive == "EventReceive"
EventTimer == "EventTimer"
EventCond == "EventCond"
EventType == { EventNone, EventReceive, EventTimer, EventCond }

NodeType == TaskType \union GatewayType \union EventType

================================================================
