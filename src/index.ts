import express from 'express';
import morgan from 'morgan';
import cors from 'cors';

import { checkModel } from './checker';
import { generateTLA } from './generator';

/**
 * Server Setup
 */

const app = express();
app.use(cors());                                 // allow cross-origin calls
app.use(morgan('tiny'));                         // log requests
app.use(express.urlencoded({ extended: true })); // set request encoding
app.use(express.json());                         // allow JSON request data

app.listen(3000, () => console.log('Listening on port 3000!'));

/**
 * Routes
 */

// model checking
app.post('/', (req, res, next) => {
  let model = req.body && req.body.diagram;
  let property = req.body && req.body.property;
  checkModel(model, property).then(output => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send(output);
  }).catch(error => {
    res.status(500);
    res.set('Content-Type', 'application/json');
    res.send({ error });
  });
});

// TLAplus generator
app.post('/convert', (req, res, next) => {
  const model = req.body && req.body.diagram;
  const property = req.body && req.body.property;
  return generateTLA(model, property).then(tla => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send({ tla });
  }).catch(error => {
    res.status(500);
    res.set('Content-Type', 'application/json');
    res.send({ error });
  });
});
