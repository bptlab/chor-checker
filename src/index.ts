import express from 'express';
import morgan from 'morgan';
import cors from 'cors';

import { checkModel } from './checker';
import { generateTLA } from './generator';

// setup server
const app = express();
app.use(cors());
app.use(morgan('tiny'));
app.use(express.urlencoded({ extended: true }));
app.use(express.json());

app.listen(3000, () => console.log('Listening on port 3000!'));

// entrypoint for model checking
app.post('/', (req, res, next) => {
  let model = req.body && req.body.diagram;
  let property = req.body && req.body.property;
  checkModel(model, property).then(output => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send(output);
  }).catch(error => {
    next(error);
  });
});

app.post('/convert', (req, res, next) => {
  const model = req.body && req.body.diagram;
  const property = req.body && req.body.property;
  return generateTLA(model, property).then(tla => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send({ tla });
  }).catch(error => {
    next(error);
  });
});
