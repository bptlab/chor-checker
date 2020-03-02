---------------- MODULE Definitions ----------------

EXTENDS Types

CONSTANTS
    Nodes, Flows, Oracles, OracleDomain, AllOracleDomains, PayloadDomain, MessageDomain,
    source, target, nodeType, defaultFlow, evaluateIntermediateEvent(_,_,_,_,_,_), evaluateFlow(_,_,_)

incoming(n) == { f \in Flows : target[f] = n }
outgoing(n) == { f \in Flows : source[f] = n }

successors(n) == { target[e] : e \in outgoing(n) }
predecessors(n) == { source[e] : e \in incoming(n) }

Tasks == { n \in Nodes : nodeType[n] = Task }

================================================================