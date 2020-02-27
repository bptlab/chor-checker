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
  <%-
    Array.from(source.entries())
     .map(entry => entry.map(e => "\"" + e + "\"").join(' :> '))
     .join(' @@ ')
  %>

target ==
  <%-
    Array.from(target.entries())
     .map(entry => entry.map(e => "\"" + e + "\"").join(' :> '))
     .join(' @@ ')
  %>

nodeType ==
   "X" :> Task
@@ "Y" :> Task
@@ "Z" :> Task
@@ "W" :> Task
@@ "E1" :> EventStart
@@ "E2" :> EventEnd
@@ "EC" :> EventConditional
@@ "ET" :> EventTimer
@@ "G1" :> GatewayExclusive
@@ "G2" :> GatewayExclusive

defaultFlow ==
  <%-
    Array.from(defaultFlow.entries())
     .map(entry => entry.map(e => "\"" + e + "\"").join(' :> '))
     .join(' @@ ')
  %>

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

INSTANCE Semantics

================================================================
