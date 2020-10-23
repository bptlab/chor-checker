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

%>
---------------- MODULE Choreography ----------------

EXTENDS TLC, Integers, Naturals, Types

VARIABLES marking

\* PUSH_ORACLES == FALSE

Tasks == {
  <%- taskIDs.map(bracketize).join(',\n  ') %>
}

Nodes == {
  <%- otherIDs.map(bracketize).join(',\n  ') %>
} \union Tasks

Flows == {
  <%- flowIDs.map(bracketize).join(',\n  ') %>
}

source ==
   <%- outputMap(source) %>

target ==
   <%- outputMap(target) %>

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

CheckProperty == <%- property %>

================================================================
