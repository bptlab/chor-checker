/**
 * Generator components.
 * Takes as an input a BPMN choreography diagram and outputs a
 * TLA+ specification for it.
 */
import fs from 'fs-extra';
import ejs from 'ejs';
import {
  Choreography,
  SequenceFlow,
  ExclusiveGateway,
  FlowNode,
  IntermediateCatchEvent,
  ConditionalEventDefinition,
  ChoreographyTask,
  TimerEventDefinition,
  SignalEventDefinition,
  Process,
  Task
} from 'bpmn-moddle';
import { is, getModel } from './helpers';
import { transpileExpression } from './parser/expression';

// prepare the TLA template
const template = ejs.compile(
  fs.readFileSync('./templates/Choreography.ejs.tla', { encoding: 'utf8' })
);

// some definitions
const SUPPORTED_FLOW_NODES : string[] = [
  'bpmn:Task',
  'bpmn:ParallelGateway',
  'bpmn:ExclusiveGateway',
  'bpmn:EventBasedGateway',
  'bpmn:StartEvent',
  'bpmn:EndEvent',
  'bpmn:IntermediateCatchEvent'
];

export function generateTLA(xml: string, property: string): Promise<string> {
  return getModel(xml).then(choreo => {
    return template(translateModel(choreo, property));
  });
}

export function translateModel(choreo: Process, property: string): Object {
  // collect relevant elements
  let nodes: FlowNode[] = <FlowNode[]> choreo.flowElements.filter(is(...SUPPORTED_FLOW_NODES));
  let flows: SequenceFlow[] = <SequenceFlow[]> choreo.flowElements.filter(is('bpmn:SequenceFlow'));
  let tasks = <Task[]> nodes.filter(is('bpmn:Task'));

  // assign more readable IDs
  let nodeMap: Map<FlowNode, string> = new Map();
  let flowMap: Map<SequenceFlow, string> = new Map();
  nodes.forEach(flowNode => {
    nodeMap.set(flowNode, flowNode.id);
  });
  flows.forEach(sequenceFlow => {
    flowMap.set(sequenceFlow, sequenceFlow.id);
  });

  // build up structures we need for the template
  // we do not want to do much processing in the template, so this includes
  // some rather basic transformations
  let taskIDs: string[] = [];
  let otherIDs: string[] = [];
  let flowIDs: string[] = [];
  let source: Map<string, string> = new Map();
  let target: Map<string, string> = new Map();
  let nodeType: Map<string, string> = new Map();
  let isSync: Map<string, string> = new Map();
  let isBlocking: Map<string, string> = new Map();

  // IDs
  nodes.forEach(node => {
    if (is('bpmn:Task')(node)) {
      taskIDs.push(nodeMap.get(node));
    } else {
      otherIDs.push(nodeMap.get(node));
    };
  })
  flows.forEach(flow => {
    flowIDs.push(flowMap.get(flow));
  })

  // define the substitutions for expressions
  //TODO replace with proper architecture pattern instead of these nested lambdas
  const literalSubstitution = literal => {
    // special values
    if (literal == 'FINISHED') {
      return 'marking = {}';
    }

    // sequence flow markings
    const flow = flows.find(flow => flow.name == literal);
    if (flow) {
      return `"${ flowMap.get(flow) }" \\in marking`;
    }
  }

  // build source/target relation
  flows.forEach(sequenceFlow => {
    source.set(flowMap.get(sequenceFlow), nodeMap.get(sequenceFlow.sourceRef));
    target.set(flowMap.get(sequenceFlow), nodeMap.get(sequenceFlow.targetRef));
  });

  // node types
  nodes.forEach(flowNode => {
    let type = '';
    if (is('bpmn:ManualTask', 'bpmn:ScriptTask', 'bpmn:ReceiveTask')(flowNode)) {
      type = 'NonBlockingTask';
    } else if (is('bpmn:Task')(flowNode)) {
      type = 'BlockingTask';
    } else if (is('bpmn:ParallelGateway')(flowNode)) {
      type = 'ParallelGateway';
    } else if (is('bpmn:ExclusiveGateway')(flowNode)) {
      type = 'ExclusiveGateway';
    } else if (is('bpmn:EventBasedGateway')(flowNode)) {
      type = 'EventBasedGateway';
    } else if (is('bpmn:StartEvent')(flowNode)) {
      type = 'StartEvent';
    } else if (is('bpmn:IntermediateCatchEvent')(flowNode)) {
      type = 'IntermediateCatchEvent';
    } else if (is('bpmn:EndEvent')(flowNode)) {
      type = 'EndEvent';
    }
    nodeType.set(nodeMap.get(flowNode), type);
  });

  // events sync/async
  nodes.forEach(flowNode => {
    if (is('bpmn:IntermediateCatchEvent')(flowNode)) {
      isSync.set(nodeMap.get(flowNode), 'FALSE');
    }    
  });

  // put all that stuff into the template
  return {
    property: transpileExpression(property, literalSubstitution),
    taskIDs,
    otherIDs,
    flowIDs,
    source,
    target,
    nodeType,
    isSync
  };
}
