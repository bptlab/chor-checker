<%

function outputMap(map) {
  if (map.size == 0) {
    return '[ i \in {} |-> {}]';
  } else {
    return Array.from(map.entries())
     .map(entry => entry.map(e => "\"" + e + "\"").join(' :> '))
     .join(' @@ ');
  }
}

%>
---------------- MODULE Choreography ----------------

EXTENDS TLC, Naturals, Types

VARIABLES marking, timestamp, oracleValues, messageValues, curTx

Nodes == {
  <%- Array.from(nodeIDs.values()).join(', ') %>
}
Flows == {
  <%- Array.from(flowIDs.values()).join(', ') %>
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
  "EURUSD",
  "WEATHER"
}
OracleDomain ==
   "EURUSD" :> { 1, 2, 3 }
@@ "WEATHER" :> { 8, 9, 10 }
AllOracleDomains == UNION { OracleDomain[o] : o \in DOMAIN OracleDomain }

MessageDomain == { 100 }

PayloadDomain == { NoPayload } \union MessageDomain \union AllOracleDomains

(* For these conditions, we can not use the variables directly. We have
   to get them as parameters. TODO Think of a better naming. *)
evaluateIntermediateEvent(n, f, ma, ti, or, me) ==
  CASE n = "ET" -> ti - ma[f][2] = 2
    [] n = "EC" -> or["WEATHER"] = 9
    [] OTHER -> FALSE

evaluateFlow(f, or, me) == FALSE
  (*CASE f = "F4" -> or["WEATHER"] = 8
    [] OTHER -> FALSE*)

INSTANCE Semantics

================================================================
