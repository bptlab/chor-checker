/**
 * Generator components.
 * Takes as an input a BPMN choreography diagram and outputs a
 * TLA+ specification for it.
 */
import { Choreography, FlowElement, SequenceFlow, ExclusiveGateway, FlowNode } from 'bpmn-moddle';
import { is, parseModdle } from './helpers';
import * as fs from 'fs';
import * as path from 'path';
import * as ejs from 'ejs';

// load files
const order = fs.readFileSync(path.join(__dirname, '/../assets/order.bpmn'), 'utf-8');
const templateText = fs.readFileSync(path.join(__dirname, '/../templates/ChoreographyTemplate.ejs.tla'), 'utf-8');

// compile template
const template = ejs.compile(templateText);


const SUPPORTED_FLOW_NODES : string[] = [
  'bpmn:ChoreographyTask',
  'bpmn:ParallelGateway',
  'bpmn:ExclusiveGateway',
  'bpmn:StartEvent',
  'bpmn:EndEvent'
  //'bpmn:IntermediateCatchEvent'
];

export async function translate(xml: string = order): Promise<string> {
  // parse model
  let choreo = await parseModdle(order).then(definitions => {
    const choreography = <Choreography> definitions.rootElements.find(is('bpmn:Choreography'));
    if (!choreography) {
      throw 'could not find a choreography instance';
    }
    return choreography;
  });

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
  
  // build default flow relation
  nodes.forEach((flowNode, index) => {
    if (is('bpmn:ExclusiveGateway')(flowNode)) {
      let exclusiveGateway = <ExclusiveGateway> flowNode;
      if (exclusiveGateway.default) {
        defaultFlow.set(nodeIDs.get(exclusiveGateway), flowIDs.get(exclusiveGateway.default));
      }
    }
  });

  // put all that stuff into the template
  return template({
    nodeIDs,
    flowIDs,
    source,
    target,
    nodeType,
    defaultFlow
  });
}


/**
 * - NO ORACLES YET
 * - NO CONDITIONS YET
 * - NEED TO FIND EXPRESSION LANGUAGE FOR SYMBOLIC ABSTRACTION
 */
