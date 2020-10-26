---------------- MODULE Types ----------------

(* Tasks *)
BlockingTask == "BlockingTask"
NonBlockingTask == "NonBlockingTask"
TaskType == { BlockingTask, NonBlockingTask }

(* Gateways *)
ParallelGateway == "ParallelGateway"
ExclusiveGateway == "ExclusiveGateway"
EventBasedGateway == "EventBasedGateway"
GatewayType == { ParallelGateway, ExclusiveGateway, EventBasedGateway }

(* Events *)
StartEvent == "StartEvent"
IntermediateCatchEvent == "IntermediateCatchEvent"
EndEvent == "EndEvent"
EventType == { StartEvent, IntermediateCatchEvent, EndEvent }

NodeType == TaskType \union GatewayType \union EventType

================================================================
