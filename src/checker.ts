import fs from 'fs-extra';
let child = require('child_process');
import { generateTLA } from './generator';
import parseState from './parser/parser';

const EXECUTION_FOLDER = './execution';
const KEEP_ARTIFACTS = true;

export async function checkModel(xml: string, property: string): Promise<Object> {
   //TODO generate better ID
  const id = new Date().getTime();
  const folder = EXECUTION_FOLDER + '/' + id;
  console.log('Start execution in', folder);

  return fs.ensureDir(folder).then(() => {
    console.log(id, 'Generated execution folder');
    return fs.copy('./environment', folder);
  }).then(() => {
    console.log(id, 'Copied execution files');
    return generateTLA(xml, property);
  }).then(tla => {
    console.log(id, 'Generated TLA');
    return fs.outputFile(folder + '/Choreography.tla', tla);
  }).then(() => {
    console.log(id, 'TLA written to file');

    // now the interesting part: running TLC
    let buffer: Buffer;
    try {
      buffer = child.execSync('java -classpath tla2tools.jar tlc2.TLC -deadlock -nowarning Choreography', { cwd: folder });
    } catch (error) {
      buffer = Buffer.concat([error.stdout, error.stderr]);
    }
    const log = buffer.toString();

    // clean up
    if (!KEEP_ARTIFACTS) {
      fs.remove(folder).then(() => {
        console.log(id, 'Cleaned up folder', folder);
      }).catch(error => {
        console.error(id, 'Error cleaning up', error);
      })
    } else {
      fs.remove(folder + '/tla2tools.jar').then(() => {
        console.log(id, 'Removed tla2tools.jar', folder);
      }).catch(error => {
        console.error(id, 'Error removing tla2tools.jar', error);
      })

      // log output to a file
      fs.outputFile(folder + '/output.log', log).then(() => {
        console.log(id, 'Wrote log to file');
      }).catch(error => {
        console.error(id, 'Error cleaning up', error);
      });
    }

    // output proper string
    console.log(id, 'TLC finished');

    // parse output
    const lines = log.split(/\r?\n/);

    let trace: Object[] = [];
    for (let i = 0; i < lines.length; i++) {
      if (/State [1-9][0-9]*: <.*?>/.test(lines[i])) {
        let j = i + 1;
        while (j < lines.length && lines[j].length >= 0) {
          j++;
        }
        const stateText = lines.slice(i + 1, j).join(' ');
        const state = parseState(stateText);
        trace.push(state);
      }
    }
    console.log(id, 'Parsed output, trace steps found:', trace.length);

    return {
      lines,
      trace
    };
  });
};