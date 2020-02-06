import express from 'express';
import * as fs from 'fs';
import * as path from 'path';
//import * as child from 'child_process';
let child = require('child_process');

import {
  is,
  parseModdle,
} from './helpers';
import { Choreography, Gateway, FlowNode } from 'bpmn-moddle';

// load XML
// const order = fs.readFileSync(path.join(__dirname, '/../assets/order.bpmn'), 'utf-8');
// const sample = fs.readFileSync(path.join(__dirname, '/../assets/sample.bpmn'), 'utf-8');

const app = express();
app.listen(3000, () => console.log('Example app listening on port 3000!'));

app.get('/', (req, res) => {
  res.send('Hello World!');
});

//
app.get('/tlc', (req, res) => {
  try {
    let foo: any = child.execSync('java -classpath tla2tools.jar tlc2.TLC -nowarning DieHard', { cwd: 'tlc' });
  }
  catch (error) {
    console.log(error.stdout.toString());
    console.log(error.stderr.toString());
  }
  
  res.send('Hello World!');
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
