const antlr4 = require('antlr4/index');
const Lexer = require('./gen/TLAplusLexer.js').TLAplusLexer;
const Parser = require('./gen/TLAplusParser.js').TLAplusParser;
import TraceVisitor from './visitor';

export default function parse(): string {
  let input = `
    /\\ marking = [SequenceFlow_0dy5er9 |-> <<FALSE, 0>>, SequenceFlow_036yo13 |-> <<TRUE, 0>>, SequenceFlow_0esuuaj |-> <<FALSE, 0>>, SequenceFlow_0xamnn2 |-> <<FALSE, 0>>]
    /\\ curTx = <<"ChoreoTx", 0, 100>>
    /\\ oracleValues = [EURUSD |-> 1, WEATHER |-> 8]
    /\\ timestamp = 0
    /\\ messageValues = [ChoreographyTask_0hy9n0g |-> 100, ChoreographyTask_1m3qduh |-> 0, ChoreographyTask_175oxwe |-> 0]
  `;
  const chars = new antlr4.InputStream(input);
  const lexer = new Lexer(chars);
  const tokens = new antlr4.CommonTokenStream(lexer);
  const parser = new Parser(tokens);
  parser.buildParseTrees = true;
  const tree = parser.def();
  const visitor = new TraceVisitor();
  const output = tree.accept(visitor);
  console.log('DONE', JSON.stringify(output, null, '  '));
  return '';
}