import express from 'express';
let child = require('child_process');

import { translate } from './generator';

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

// entrypoint for the TLA converter
app.get('/convert', (req, res) => {
  translate().then(tla => {
    res.set('Content-Type', 'text/plain');
    res.send(tla);
  }).catch(error => {
    res.set('Content-Type', 'text/plain');
    res.send(error.message);
    throw error;
  });
});
