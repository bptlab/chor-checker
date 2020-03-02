---------------- MODULE Definitions ----------------

EXTENDS Types

CONSTANTS
    PUSH_ORACLES,
    Tasks, Nodes, Flows,
    Oracles, OracleDomain, AllOracleDomains,
    MessageDomain, AllMessageDomains,
    PayloadDomain,
    source, target, nodeType, defaultFlow, evaluateIntermediateEvent(_,_,_,_,_,_), evaluateFlow(_,_,_)

incoming(n) == { f \in Flows : target[f] = n }
outgoing(n) == { f \in Flows : source[f] = n }

successors(n) == { target[e] : e \in outgoing(n) }
predecessors(n) == { source[e] : e \in incoming(n) }

================================================================
