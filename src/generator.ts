/**
 * Generator components.
 * Takes as an input a BPMN choreography diagram and outputs a
 * TLA+ specification for it.
 */
import * as fs from 'fs';
import * as path from 'path';
import * as ejs from 'ejs';
import { Choreography, SequenceFlow, ExclusiveGateway, FlowNode } from 'bpmn-moddle';
import { is, getModel } from './helpers';

// load fallback file for testing
const order = fs.readFileSync(path.join(__dirname, '/../assets/order.bpmn'), 'utf-8');

// prepare the TLA template
const template = ejs.compile(
  fs.readFileSync(path.join(__dirname, '/../templates/Choreography.ejs.tla'), 'utf-8')
);

// some definitions
const SUPPORTED_FLOW_NODES : string[] = [
  'bpmn:ChoreographyTask',
  'bpmn:ParallelGateway',
  'bpmn:ExclusiveGateway',
  'bpmn:StartEvent',
  'bpmn:EndEvent'
  //'bpmn:IntermediateCatchEvent'
];

export function generateTLA(xml: string = order): Promise<string> {
  return getModel(xml).then(choreo => {
    return template(translateModel(choreo));
  });
}

export function translateModel(choreo: Choreography): Object {
  // collect relevant elements
  let nodes: FlowNode[] = <FlowNode[]> choreo.flowElements.filter(is(...SUPPORTED_FLOW_NODES));
  let flows: SequenceFlow[] = <SequenceFlow[]> choreo.flowElements.filter(is('bpmn:SequenceFlow'));

  // assign more readable IDs
  let nodeIDs: Map<FlowNode, string> = new Map();
  let flowIDs: Map<SequenceFlow, string> = new Map();
  nodes.forEach((flowNode, index) => {
    // nodeIDs.set(flowNode, 'N' + index);
    nodeIDs.set(flowNode, flowNode.id);
  });
  flows.forEach((sequenceFlow, index) => {
    // flowIDs.set(sequenceFlow, 'F' + index);
    flowIDs.set(sequenceFlow, sequenceFlow.id);
  });

  // build up structures we need for the template
  let source: Map<string, string> = new Map();
  let target: Map<string, string> = new Map();
  let nodeType: Map<string, string> = new Map();
  let defaultFlow: Map<string, string> = new Map();

  // build source/target relation
  flows.forEach(sequenceFlow => {
    source.set(flowIDs.get(sequenceFlow), nodeIDs.get(sequenceFlow.sourceRef));
    target.set(flowIDs.get(sequenceFlow), nodeIDs.get(sequenceFlow.targetRef));
  });
  
  // build default flow relation and node types
  nodes.forEach((flowNode, index) => {
    if (is('bpmn:ExclusiveGateway')(flowNode)) {
      let exclusiveGateway = <ExclusiveGateway> flowNode;
      let flow: SequenceFlow;
      if (exclusiveGateway.default) {
        flow = exclusiveGateway.default;
      } else {
        // if no default flow was defined, just pick any --- this is just to
        // simplify the TLA code later and has no consequences otherwise since
        // we assume that a default flow is defined via the well-formedness
        // property of the choreography
        flow = exclusiveGateway.outgoing[0];
      }
      defaultFlow.set(nodeIDs.get(exclusiveGateway), flowIDs.get(flow));
    }

    let type = '';
    if (is('bpmn:ChoreographyTask')(flowNode)) {
      type = 'Task';
    } else if (is('bpmn:ParallelGateway')(flowNode)) {
      type = 'GatewayParallel';
    } else if (is('bpmn:ExclusiveGateway')(flowNode)) {
      type = 'GatewayExclusive';
    } else if (is('bpmn:StartEvent')(flowNode)) {
      type = 'EventStart';
    } else if (is('bpmn:EndEvent')(flowNode)) {
      type = 'EventEnd';
    }
    nodeType.set(nodeIDs.get(flowNode), type);
  });

  // put all that stuff into the template
  return {
    nodeIDs,
    flowIDs,
    source,
    target,
    nodeType,
    defaultFlow
  };
}

/**
 * - NO ORACLES YET
 * - NO CONDITIONS YET
 * - NO INTERMEDIATE EVENTS YET
 * - NEED TO FIND EXPRESSION LANGUAGE FOR SYMBOLIC ABSTRACTION
 */
