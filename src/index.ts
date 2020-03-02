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
  let term = req.body && req.body.term;
  checkModel(model, term).then(output => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send(output);
  }).catch(error => {
    next(error);
  });
});

app.post('/convert', (req, res, next) => {
  const model = req.body && req.body.diagram;
  return generateTLA(model).then(tla => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send({ tla });
  }).catch(error => {
    next(error);
  });
});

app.get('/convert', (req, res, next) => {
  return generateTLA().then(tla => {
    res.status(200);
    res.set('Content-Type', 'application/json');
    res.send({ tla });
  }).catch(error => {
    next(error);
  });
});
