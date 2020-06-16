---------------- MODULE Definitions ----------------

EXTENDS Types

CONSTANTS
    PUSH_ORACLES, MAX_TIMESTAMP, PAST,
    Tasks, Nodes, Flows,
    Oracles, OracleDomain, AllOracleDomains,
    MessageDomain, AllMessageDomains,
    PayloadDomain,
    source, target, nodeType, defaultFlow,
    evaluateEventAt(_,_,_,_,_,_), evaluateFlow(_,_,_)

(* There should always be exactly one incoming and outgoing sequence flow.
   These operators should not be called on nodes where this is not guaranteed. *)
incoming(n) == CHOOSE f \in Flows : target[f] = n
outgoing(n) == CHOOSE f \in Flows : source[f] = n

successor(n) == target[outgoing(n)]
predecessor(n) == source[incoming(n)]

(* Siblings are all nodes which follow the same event-based gateway.
   There are no siblings if the node does not follow such a gateway. *)
siblings[n \in Nodes] ==
  IF nodeType[predecessor(n)] = GatewayEvent
  THEN { target[f] : f \in { ff \in Flows : source[ff] = predecessor(n) } } \ { n }
  ELSE { }

================================================================
