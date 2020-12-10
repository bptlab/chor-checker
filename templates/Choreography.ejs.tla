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
     .join('\n@@ ');
  }
}

function outputDetectMap(map) {
  if (map.size == 0) {
    return 'FALSE';
  } else {
    return 'CASE ' + Array.from(map.entries())
     .map(entry => 'n = ' + bracketize(entry[0]) + ' -> ' + entry[1])
     .join('\n [] ') + '\n [] OTHER -> FALSE';
  }
}

%>
---------------- MODULE Choreography ----------------

EXTENDS TLC, Integers, Naturals, Types

VARIABLES time, marking, age

\* PUSH_ORACLES == FALSE

Nodes == {
  <%- nodeIDs.map(bracketize).join(',\n  ') %>
}

Flows == {
  <%- flowIDs.map(bracketize).join(',\n  ') %>
}

source ==
   <%- outputMap(source) %>

target ==
   <%- outputMap(target) %>

messageFlowTarget ==
   <%- outputMap(messageFlowTarget) %>

nodeType ==
   <%- nodeType.size == 0 ? '[ i \\in {} |-> {}]' :
    Array.from(nodeType.entries())
     .map(entry => entry.map((e,i) => i == 0 ? "\"" + e + "\"" : e).join(' :> '))
     .join('\n@@ ')
  %>

isSync ==
   <%- isSync.size == 0 ? '[ i \\in {} |-> {}]' :
    Array.from(isSync.entries())
     .map(entry => entry.map((e,i) => i == 0 ? "\"" + e + "\"" : e).join(' :> '))
     .join('\n@@ ')
  %>

detect(n, ta, tc) ==
   <%- outputDetectMap(detect) %>

CheckProperty == <%- property %>

================================================================
