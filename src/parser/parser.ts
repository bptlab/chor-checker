const antlr4 = require('antlr4/index');
const Lexer = require('./gen/TLAplusLexer.js').TLAplusLexer;
const Parser = require('./gen/TLAplusParser.js').TLAplusParser;
import TraceVisitor from './visitor';

export default function parseState(input: string): Object {
  const chars = new antlr4.InputStream(input);
  const lexer = new Lexer(chars);
  const tokens = new antlr4.CommonTokenStream(lexer);
  const parser = new Parser(tokens);
  parser.buildParseTrees = true;
  const tree = parser.def();
  const visitor = new TraceVisitor();
  const output = tree.accept(visitor);
  return output;
}
