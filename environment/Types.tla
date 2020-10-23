---------------- MODULE Types ----------------

(* choreography types *)
Task == "Task"
ParallelGateway == "ParallelGateway"
ExclusiveGateway == "ExclusiveGateway"
EventBasedGateway == "EventBasedGateway"
StartEvent == "StartEvent"
IntermediateCatchEvent == "IntermediateCatchEvent"
EndEvent == "EndEvent"

GatewayType == { ParallelGateway, ExclusiveGateway, EventBasedGateway }
EventType == { StartEvent, IntermediateCatchEvent, EndEvent }

NodeType == { Task } \union GatewayType \union EventType

================================================================
