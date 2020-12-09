/**
 * Generator components.
 * Takes as an input a BPMN collaboration diagram and outputs a
 * TLA+ specification for it.
 */
import fs from 'fs-extra';
import ejs from 'ejs';
import BpmnModdle, {
  SequenceFlow,
  FlowNode,
  IntermediateCatchEvent,
  ConditionalEventDefinition,
  TimerEventDefinition,
  SignalEventDefinition,
  Process,
  Task,
  Collaboration,
  MessageFlow,
  SendTask
} from 'bpmn-moddle';
import { is } from './helpers';
import { transpileExpression } from './parser/expression';

// prepare the TLA template
const template = ejs.compile(
  fs.readFileSync('./templates/Choreography.ejs.tla', { encoding: 'utf8' })
);

// some definitions
const SUPPORTED_FLOW_NODES : string[] = [
  'bpmn:UserTask',
  'bpmn:ScriptTask',
  'bpmn:SendTask',
  'bpmn:ParallelGateway',
  'bpmn:ExclusiveGateway',
  'bpmn:EventBasedGateway',
  'bpmn:StartEvent',
  'bpmn:EndEvent',
  'bpmn:IntermediateCatchEvent'
];

export async function generateTLA(xml: string, property: string): Promise<Object> {
  const moddle = new BpmnModdle();
  // @ts-ignore bpmn-moddle types are not yet updated for promises
  const definitions : Definitions = (await moddle.fromXML(xml)).rootElement;

  const processes = <Process[]> definitions.rootElements.filter(is('bpmn:Process'));
  if (!processes || processes.length == 0) {
    throw 'could not find a choreography instance';
  }

  const collabs = <Collaboration[]> definitions.rootElements.filter(is('bpmn:Collaboration'));
  let messageFlows : MessageFlow[] = [];
  if (collabs) {
    messageFlows = collabs.map(c => c.messageFlows).flat();
  }

  // collect relevant elements
  let nodes: FlowNode[] = <FlowNode[]> processes.map(p => p.flowElements.filter(is(...SUPPORTED_FLOW_NODES))).flat();
  let flows: SequenceFlow[] = <SequenceFlow[]> processes.map(p => p.flowElements.filter(is('bpmn:SequenceFlow'))).flat();

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
  let nodeIDs: string[] = [];
  let flowIDs: string[] = [];
  let source: Map<string, string> = new Map();
  let target: Map<string, string> = new Map();
  let messageFlowTarget: Map<string, string> = new Map();
  let nodeType: Map<string, string> = new Map();
  let isSync: Map<string, string> = new Map();
  let isBlocking: Map<string, string> = new Map();

  // IDs
  nodes.forEach(node => {
    nodeIDs.push(nodeMap.get(node));
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

  // message flows
  messageFlows.forEach(m => {
    if (is('bpmn:SendTask')(m.sourceRef) && is('bpmn:IntermediateCatchEvent')(m.targetRef)) {
      messageFlowTarget.set(
        nodeMap.get(<SendTask> m.sourceRef),
        nodeMap.get(<IntermediateCatchEvent> m.targetRef)
      );
    }
  });

  // node types
  nodes.forEach(flowNode => {
    let type = '';

    if (is('bpmn:UserTask')(flowNode)) {
      type = 'TaskUser';
    } else if (is('bpmn:ScriptTask')(flowNode)) {
      type = 'TaskScript';
    } else if (is('bpmn:SendTask')(flowNode)) {
      type = 'TaskSend';
    } else if (is('bpmn:ParallelGateway')(flowNode)) {
      type = 'GateParallel';
    } else if (is('bpmn:ExclusiveGateway')(flowNode)) {
      type = 'GateExclusive';
    } else if (is('bpmn:EventBasedGateway')(flowNode)) {
      type = 'GateDeferred';
    } else if (is('bpmn:StartEvent')(flowNode)) {
      type = 'EventNone';
    } else if (is('bpmn:EndEvent')(flowNode)) {
      type = 'EventNone';
    } else if (is('bpmn:IntermediateCatchEvent')(flowNode)) {
      const ev : IntermediateCatchEvent = <IntermediateCatchEvent> flowNode;
      if (ev.eventDefinitions.length > 0) {
        const def = ev.eventDefinitions[0];
        if (is('bpmn:TimerEventDefinition')(def)) {
          type = 'EventTimer';
        } else if (is('bpmn:ConditionalEventDefinition')(def)) {
          type = 'EventCond';
        } else if (is('bpmn:MessageEventDefinition')(def)) {
          type = 'EventReceive';
        } else {
          throw 'Unsupported event ' + flowNode.id;
        }
      }
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
  return template({
    property: transpileExpression(property, literalSubstitution),
    nodeIDs,
    flowIDs,
    source,
    target,
    messageFlowTarget,
    nodeType,
    isSync
  });
}
