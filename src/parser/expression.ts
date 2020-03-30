import jsep from "jsep";

/**
 * Language Extension
 */
jsep.addUnaryOp('G'); // global temporal operator
jsep.addUnaryOp('F'); // future (eventually) temporal operator
jsep.addBinaryOp('~>', 0); // leads to operator of TLA
jsep.addBinaryOp('=>', 6); // implication operator of TLA
jsep.addBinaryOp('<=>', 6); // equivalence operator of TLA

/**
 * Transpile an expression defined in the BPMN model via the Javascript-like syntax
 * we use to a valid TLAplus expression. Includes subsitution capabilities to reference
 * sequence flows etc. without knowing their IDs.
 *
 * @param expr Javascript-like expression
 * @param literalSubstitution A function that is called on each literal and updates the
 *  literal value with the return value
 */
export function transpileExpression(expr: string, literalSubstitution: Function): string {
  const ast = jsep(expr);
  return walkExpression(ast, literalSubstitution);
}

function walkExpression(expr: jsep.Expression, literalSubstitution: Function): string {
  let output: string;
  let operator: string;
  switch (expr.type) {
    case 'BinaryExpression':
      const binaryExpr = <jsep.BinaryExpression> expr;
      operator = binaryExpr.operator;
      switch (binaryExpr.operator) {
        case '==':
          operator = '=';
          break;
        case '!=':
          operator = '/=';
          break;
        case '+':
        case '-':
        case '*':
        case '/':
        case '~>':
        case '=>':
        case '<=>':
          operator = binaryExpr.operator;
          break;
        default:
          throw 'unexpected operator in binary expression: ' + operator;
      }
      output = walkExpression(binaryExpr.left, literalSubstitution)
        + operator
        + walkExpression(binaryExpr.right, literalSubstitution);
      break;

    case 'LogicalExpression':
      const logicalExpr = <jsep.LogicalExpression> expr;
      operator = logicalExpr.operator;
      switch (logicalExpr.operator) {
        case '||':
          operator = '\\/';
          break;
        case '&&':
          operator = '/\\';
          break;
        default:
          throw 'unexpected operator in logical expression: ' + operator;
      }
      output = walkExpression(logicalExpr.left, literalSubstitution)
        + operator
        + walkExpression(logicalExpr.right, literalSubstitution);
      break;

    case 'UnaryExpression':
      const unaryExpr = <jsep.UnaryExpression> expr;
      switch (unaryExpr.operator) {
        case '!':
          operator = '~';
          break;
        case 'G':
          operator = '[]';
          break;
        case 'F':
          operator = '<>';
          break;
        default:
          throw 'unexpected operator in unary expression ' + unaryExpr.operator;
      }
      output = operator + walkExpression(unaryExpr.argument, literalSubstitution);
      break;

    case 'Identifier':
      // lookup oracles
      const identifier = <jsep.Identifier> expr;
      const substitution = literalSubstitution(identifier.name);
      if (substitution) {
        return substitution;
      }
      throw 'unexpected identifier, neither oracle nor message: ' + identifier.name;

    case 'Literal':
      return (<jsep.Literal> expr).raw;

    default:
      throw 'unexpected expression: ' + JSON.stringify(expr);
  }

  // enforce full bracketization for non-identifiers or non-literals
  return '(' + output + ')';
}
