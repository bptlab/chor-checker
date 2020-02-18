---------------- MODULE Definitions ----------------

EXTENDS Types

CONSTANT Nodes, Flows, source, target, nodeType

incoming(n) == { f \in Flows : target[f] = n }
outgoing(n) == { f \in Flows : source[f] = n }

successors(n) == { target[e] : e \in outgoing(n) }
predecessors(n) == { source[e] : e \in incoming(n) }

================================================================
