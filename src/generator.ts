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
  SignalEventDefinition
} from 'bpmn-moddle';
import { is, getModel } from './helpers';
import { transpileExpression } from './parser/expression';

// prepare the TLA template
const template = ejs.compile(
  fs.readFileSync('./templates/Choreography.ejs.tla', { encoding: 'utf8' })
);

// some definitions
const SUPPORTED_FLOW_NODES : string[] = [
  'bpmn:ChoreographyTask',
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

export function translateModel(choreo: Choreography, property: string): Object {
  // collect relevant elements
  let nodes: FlowNode[] = <FlowNode[]> choreo.flowElements.filter(is(...SUPPORTED_FLOW_NODES));
  let flows: SequenceFlow[] = <SequenceFlow[]> choreo.flowElements.filter(is('bpmn:SequenceFlow'));
  let tasks = <ChoreographyTask[]> nodes.filter(is('bpmn:ChoreographyTask'));

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
  let defaultFlow: Map<string, string> = new Map();
  let flowConditions: Map<string, string> = new Map();
  let eventConditions: Map<string, string> = new Map();
  let oracles: Array<any> = [];
  let messageDomains: Map<string, Array<number>> = new Map();

  // IDs
  nodes.forEach(node => {
    if (is('bpmn:ChoreographyTask')(node)) {
      taskIDs.push(nodeMap.get(node));
    } else {
      otherIDs.push(nodeMap.get(node));
    };
  })
  flows.forEach(flow => {
    flowIDs.push(flowMap.get(flow));
  })

  // determine message domains
  // we assume each task is assigned to exactly one message
  let messageToTask: Map<string, string> = new Map();
  tasks.forEach(task => {
    let domain;
    const message = task.messageFlowRef[0].messageRef;
    if (message) {
      const itemDefinition = message.itemRef;
      if (itemDefinition) {
        try {
          domain = JSON.parse(itemDefinition.structureRef);
        } catch (error) {
          // just use the default domain
          console.warn('Could not parse ItemDefinition', message, itemDefinition);
        }
      }

      // also calculate the mapping from message name to task ID
      if (message.name) {
        messageToTask.set(message.name, nodeMap.get(task));
      }
    }
    if (!domain) {
      domain = [ 0 ];
    }
    messageDomains.set(nodeMap.get(task), domain);
  });

  // check if we have oracles involved
  if (choreo.documentation) {
    const doc = JSON.parse(choreo.documentation.map(d => d.text).join() || '{}');
    if (doc && doc.oracles) {
      oracles = doc.oracles;
    }
  }

  // define the substitutions for expressions
  //TODO replace with proper architecture pattern instead of these nested lambdas
  const literalSubstitution = (short: Boolean = true) => {
    return literal => {
      // special values
      if (literal == 'NO_TRANSACTION') {
        if (short) {
          throw 'NO_TRANSACTION can only be referenced from property perspective';
        } else {
          return 'curTx[2] = Empty';
        }
      }

      // oracle values
      if (oracles.find(oracle => oracle.name == literal)) {
        if (short) {
          return 'or["' + literal + '"][1]';
        } else {
          return 'oracleValues["' + literal + '"][1]';
        }
      };
  
      // message values
      const task = tasks.find(task => {
        const messageFlow = task.messageFlowRef.find(messageFlow => messageFlow.sourceRef == task.initiatingParticipantRef);
        if (messageFlow) {
          const message = messageFlow.messageRef;
          if (message && message.name) {
            if (message.name == literal) {
              return true;
            }
          }
        }
      });
      if (task) {
        if (short) {
          return 'me["' + nodeMap.get(task) + '"]';
        } else {
          return 'messageValues["' + nodeMap.get(task) + '"]';
        }
      }
  
      // sequence flow markings
      const flow = flows.find(flow => flow.name == literal);
      if (flow) {
        if (short) {
          return 'ma["' + flowMap.get(flow) + '"][1]';
        } else {
          return 'marking["' + flowMap.get(flow) + '"][1]';
        }
      }
    }
  }

  // build source/target relation
  flows.forEach(sequenceFlow => {
    source.set(flowMap.get(sequenceFlow), nodeMap.get(sequenceFlow.sourceRef));
    target.set(flowMap.get(sequenceFlow), nodeMap.get(sequenceFlow.targetRef));
  });
  
  // build default flow relation and node types
  nodes.forEach(flowNode => {
    if (is('bpmn:ExclusiveGateway')(flowNode)) {
      let exclusiveGateway = <ExclusiveGateway> flowNode;

      // conditions
      exclusiveGateway.outgoing.forEach(outgoing => {
        if (outgoing.conditionExpression && outgoing.conditionExpression.body) {
          flowConditions.set(
            flowMap.get(outgoing),
            transpileExpression(outgoing.conditionExpression.body, literalSubstitution())
          );
        }
      });

      // default flow
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
      defaultFlow.set(nodeMap.get(exclusiveGateway), flowMap.get(flow));
    }

    let type = '';
    if (is('bpmn:ChoreographyTask')(flowNode)) {
      type = 'Task';
    } else if (is('bpmn:ParallelGateway')(flowNode)) {
      type = 'GatewayParallel';
    } else if (is('bpmn:ExclusiveGateway')(flowNode)) {
      type = 'GatewayExclusive';
    } else if (is('bpmn:EventBasedGateway')(flowNode)) {
      type = 'GatewayEvent';
    } else if (is('bpmn:StartEvent')(flowNode)) {
      type = 'EventStart';
    } else if (is('bpmn:IntermediateCatchEvent')(flowNode)) {
      type = 'EventIntermediate';
    } else if (is('bpmn:EndEvent')(flowNode)) {
      type = 'EventEnd';
    }
    nodeType.set(nodeMap.get(flowNode), type);
  });

  // translate intermediate catch events
  nodes.filter(is('bpmn:IntermediateCatchEvent')).forEach(flowNode => {
    const event = <IntermediateCatchEvent> flowNode;
    const definition = event.eventDefinitions[0];

    if (is('bpmn:TimerEventDefinition')(definition)) {
      const timerDef = (<TimerEventDefinition> definition);
      let expression;
      if (timerDef.timeDuration) {
        expression = `(ti >= ma[f][2] + ${ timerDef.timeDuration.body })`;
      } else if (timerDef.timeDate) {
        //TODO research whether this is the actual semantics of absolute timer events --- can they fire after the exact time has passed?
        expression = `(ti = ${ timerDef.timeDate.body })`;
      }
      eventConditions.set(nodeMap.get(event), expression);
    } else if (is('bpmn:ConditionalEventDefinition')(definition)) {
      const expression = (<ConditionalEventDefinition> definition).condition.body;
      eventConditions.set(
        nodeMap.get(event),
        transpileExpression(expression, literalSubstitution())
      );
    } else if (is('bpmn:SignalEventDefinition')(definition)) {
      const signal = (<SignalEventDefinition> definition).signalRef;

      // add an oracle for the signal if not already done
      if (!oracles.find(oracle => oracle.name == signal.name)) {
        oracles.push({ name: signal.name, values: [0] });
      }

      // add a timed condition for this event
      eventConditions.set(
        nodeMap.get(event),
        `(ma[f][2] <= or["${ signal.name }"][2])`
      );
    }
  });

  // put all that stuff into the template
  return {
    property: transpileExpression(property, literalSubstitution(false)),
    taskIDs,
    otherIDs,
    flowIDs,
    source,
    target,
    nodeType,
    defaultFlow,
    flowConditions,
    eventConditions,
    oracles,
    messageDomains
  };
}
