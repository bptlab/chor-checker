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

PUSH_ORACLES == TRUE

Tasks == {
  <%- taskIDs.map(bracketize).join(', ') %>
}

Nodes == {
  <%- otherIDs.map(bracketize).join(', ') %>
} \union Tasks

Flows == {
  <%- flowIDs.map(bracketize).join(', ') %>
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
<% if (oracles.length == 0) { _%>
  [i \in {} |-> {}]
<% } else { _%>
{
  <%- oracles.map(o => [bracketize(o.name), '{' + o.values.join(', ') + '}'].join(' :> ')).join(' @@ ') %>
}
<% } %>

AllOracleDomains == UNION { OracleDomain[o] : o \in DOMAIN OracleDomain }

MessageDomain ==
  <%- Array.from(messageDomains.entries()).map(m => [bracketize(m[0]), '{' + m[1].join(', ') + '}'].join(' :> ')).join(' @@ ') %>
AllMessageDomains == UNION { MessageDomain[m] : m \in DOMAIN MessageDomain }

PayloadDomain == { NoPayload } \union AllMessageDomains \union AllOracleDomains

(* For these conditions, we can not use the variables directly. We have
   to get them as parameters. *)
evaluateIntermediateEvent(n, f, ma, ti, or, me) ==
<% if (eventConditions.size == 0) { _%>
  FALSE
<% } else { _%>
  CASE
  <%- Array.from(eventConditions.entries()).map(e => ['n=' + bracketize(e[0]), e[1]].join(' -> ')).join(' [] ') %>
  [] OTHER -> FALSE
<% } %>

evaluateFlow(f, or, me) ==
<% if (flowConditions.size == 0) { _%>
  FALSE
<% } else { _%>
  CASE
  <%- Array.from(flowConditions.entries()).map(e => ['f=' + bracketize(e[0]), e[1]].join(' -> ')).join(' [] ') %>
  [] OTHER -> FALSE
<% } %>

INSTANCE Semantics

================================================================
