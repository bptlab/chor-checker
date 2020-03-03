/**
 * Generator components.
 * Takes as an input a BPMN choreography diagram and outputs a
 * TLA+ specification for it.
 */
import * as fs from 'fs';
import * as path from 'path';
import * as ejs from 'ejs';
import jsep from "jsep";
import { Choreography, SequenceFlow, ExclusiveGateway, FlowNode, IntermediateCatchEvent, ConditionalEventDefinition, ChoreographyTask, TimerEventDefinition } from 'bpmn-moddle';
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
  'bpmn:EventBasedGateway',
  'bpmn:StartEvent',
  'bpmn:EndEvent',
  'bpmn:IntermediateCatchEvent'
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
  let oracles: Array<object> = [];
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
  })

  // check if we have oracles involved
  if (choreo.documentation) {
    const doc = JSON.parse(choreo.documentation.map(d => d.text).join());
    if (doc && doc.oracles) {
      oracles = doc.oracles;
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
            transpileExpression(outgoing.conditionExpression.body, oracles, messageToTask)
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
        expression = 'ti >= ma[f][2] + ' + timerDef.timeDuration.body;
      } else if (timerDef.timeDate) {
        expression = 'ti = ' + timerDef.timeDate.body;
      }
      eventConditions.set(nodeMap.get(event), expression);
    } else if (is('bpmn:ConditionalEventDefinition')(definition)) {
      const expression = (<ConditionalEventDefinition> definition).condition.body;
      eventConditions.set(
        nodeMap.get(event),
        transpileExpression(expression, oracles, messageToTask)
      );
    }
  });

  // put all that stuff into the template
  return {
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

function transpileExpression(expr: string, oracles: Array<object>, messageToTask: Map<string, string>): string {
  return walkExpression(jsep(expr), oracles, messageToTask);
}

function walkExpression(expr: jsep.Expression, oracles: Array<any>, messageToTask: Map<string, string>): string {
  let output: string;
  let operator: string;
  switch (expr.type) {
    case 'BinaryExpression':
      const binaryExpr = <jsep.BinaryExpression> expr;
      operator = binaryExpr.operator;
      switch (binaryExpr.operator) {
        case '==':
          operator = '=';
          break;
        case '+':
        case '-':
        case '*':
        case '/':
          operator = binaryExpr.operator;
          break;
        default:
          throw 'unexpected operator in binary expression: ' + operator;
      }
      output = walkExpression(binaryExpr.left, oracles, messageToTask)
        + operator
        + walkExpression(binaryExpr.right, oracles, messageToTask);
      break;

    case 'LogicalExpression':
      const logicalExpr = <jsep.LogicalExpression> expr;
      operator = logicalExpr.operator;
      switch (logicalExpr.operator) {
        case '||':
          operator = '\\/';
          break;
        case '&&':
          operator = '/\\';
          break;
        default:
          throw 'unexpected operator in logical expression: ' + operator;
      }
      output = walkExpression(logicalExpr.left, oracles, messageToTask)
        + operator
        + walkExpression(logicalExpr.right, oracles, messageToTask);
      break;

    case 'UnaryExpression':
      const unaryExpr = <jsep.UnaryExpression> expr;
      switch (unaryExpr.operator) {
        case '!':
          output = '~' + walkExpression(unaryExpr.argument, oracles, messageToTask);
          break;
        default:
          throw 'unexpected operator in unary expression ' + unaryExpr.operator;
      }
      break;

    case 'Identifier':
      // lookup oracles
      const identifier = <jsep.Identifier> expr;
      if (oracles.find(oracle => oracle.name == identifier.name)) {
        return 'or["' + identifier.name + '"]';
      } else if (messageToTask.has(identifier.name)) {
        return 'me["' + messageToTask.get(identifier.name) + '"]';
      }
      throw 'unexpected identifier, neither oracle nor message: ' + identifier.name;

    case 'Literal':
      return (<jsep.Literal> expr).raw;

    default:
      throw 'unexpected expression: ' + expr;
  }

  // enforce full bracketization for non-identifiers or non-literals
  return '(' + output + ')';
}
