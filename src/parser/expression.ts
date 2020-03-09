import jsep from "jsep";
jsep.addUnaryOp('G');
jsep.addUnaryOp('F');

export default function transpileExpression(expr: string, literalSubstitution: Function): string {
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
        case '+':
        case '-':
        case '*':
        case '/':
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
          output = '~' + walkExpression(unaryExpr.argument, literalSubstitution);
          break;
        case 'G':
          output = '[]' + walkExpression(unaryExpr.argument, literalSubstitution);
          break;
        case 'F':
          output = '<>' + walkExpression(unaryExpr.argument, literalSubstitution);
          break;
        default:
          throw 'unexpected operator in unary expression ' + unaryExpr.operator;
      }
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
      throw 'unexpected expression: ' + expr;
  }

  // enforce full bracketization for non-identifiers or non-literals
  return '(' + output + ')';
}
