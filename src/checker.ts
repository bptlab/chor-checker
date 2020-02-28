import * as path from 'path';
import { generateTLA } from './generator';
let child = require('child_process');

export async function checkModel(xml: string, term: string): Promise<string> {
  // parse model
  return generateTLA(xml).then(tla => {
    try {
      let output : Buffer;
      output = child.execSync('java -classpath tla2tools.jar tlc2.TLC -deadlock -nowarning Choreography', { cwd: 'templates' });
      return output.toString();
    }
    catch (error) {
      // trace output
      //TODO parse
      const trace = Buffer.concat([error.stdout, error.stderr]);
      return trace.toString();
    }
  });
};