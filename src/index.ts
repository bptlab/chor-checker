import express from 'express';
import * as fs from 'fs';
import * as path from 'path';
let child = require('child_process');

import {
  is,
  parseModdle,
} from './helpers';
import { Choreography, Gateway, FlowNode } from 'bpmn-moddle';

// load XML
const order = fs.readFileSync(path.join(__dirname, '/../assets/request.bpmn'), 'utf-8');

// setup server
const app = express();
app.listen(3000, () => console.log('Listening on port 3000!'));

// entrypoint for model checking
app.get('/', (req, res) => {
  let output : Buffer;
  try {
    output = child.execSync('java -classpath tla2tools.jar tlc2.TLC -deadlock -nowarning Choreography', { cwd: 'templates' });
  }
  catch (error) {
    output = Buffer.concat([error.stdout, error.stderr]);
  }
  res.set('Content-Type', 'text/plain');
  res.send(output);
});

// // route that returns all the gateways from `sample`
// app.get('/gateways', (req, res) => {
//   parseModdle(sample).then((definitions) => {
//     const choreography = <Choreography> definitions.rootElements.find(is('bpmn:Choreography'));
//     if (!choreography) {
//       return res.status(501).send('could not find a choreography instance');
//     }
//     const gateways = <Gateway[]> choreography.flowElements.filter(is('bpmn:Gateway'));
//     res.status(201).send(gateways);
//   });
// });

// // route that returns all the predecessors/successors of flow nodes from `order`
// // example: http://localhost:3000/neighbors/ExclusiveGateway_0f1f4ys
// app.get('/neighbors/:id', (req, res) => {
//   parseModdle(order).then((definitions) => {
//     const choreography = <Choreography> definitions.rootElements.find(is('bpmn:Choreography'));
//     if (!choreography) {
//       return res.status(501).send('could not find a choreography instance');
//     }
//     const id = req.params['id'];
//     const element = <FlowNode> choreography.flowElements.find((element) => element.id == id);
//     if (!element) {
//       return res.status(501).send('could not find element with specified id');
//     }
//     const predecessors = <FlowNode[]> element.incoming.map(flow => flow.sourceRef);
//     const successors = <FlowNode[]> element.outgoing.map(flow => flow.targetRef);
//     res.status(201).send({
//       predecessors: predecessors,
//       successors: successors
//     });
//   });
// });
