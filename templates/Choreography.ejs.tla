<%

function bracketize(str) {
    return "\"" + str + "\"";
}

function outputMap(map) {
  if (map.size == 0) {
    //TODO: think about a proper output if there are no entries
    return 'FALSE';
  } else {
    return Array.from(map.entries())
     .map(entry => entry.map(bracketize).join(' :> '))
     .join(' @@ ');
  }
}

%>
---------------- MODULE Choreography ----------------

EXTENDS TLC, Naturals, Types

VARIABLES marking, timestamp, oracleValues, messageValues, curTx

Nodes == {
  <%- Array.from(nodeIDs.values()).map(bracketize).join(', ') %>
}
Flows == {
  <%- Array.from(flowIDs.values()).map(bracketize).join(', ') %>
}

source ==
  <%- outputMap(source) %>

target ==
  <%- outputMap(target) %>

nodeType ==
  <%- nodeType.size == 0 ? '[ i \in {} |-> {}]' :
    Array.from(nodeType.entries())
     .map(entry => entry.map((e,i) => i == 0 ? "\"" + e + "\"" : e).join(' :> '))
     .join(' @@ ')
  %>

defaultFlow ==
  <%- outputMap(defaultFlow) %>

Oracles == {
  <%- oracles.map(o => o.name).map(bracketize).join(', ') %>
}
OracleDomain ==
  <%- oracles.map(o => [bracketize(o.name), '{' + o.values.join(', ') + '}'].join(' :> ')).join(' @@ ') %>
AllOracleDomains == UNION { OracleDomain[o] : o \in DOMAIN OracleDomain }

MessageDomain == { 100 }

PayloadDomain == { NoPayload } \union MessageDomain \union AllOracleDomains

(* For these conditions, we can not use the variables directly. We have
   to get them as parameters. TODO Think of a better naming. *)
evaluateIntermediateEvent(n, f, ma, ti, or, me) == FALSE

evaluateFlow(f, or, me) == CASE
  <%- Array.from(flowConditions.entries()).map(e => ['f=' + bracketize(e[0]), e[1]].join(' -> ')).join(' [] ') %>
  [] OTHER -> FALSE

INSTANCE Semantics

================================================================