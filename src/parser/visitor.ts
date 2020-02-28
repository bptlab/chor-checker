import { TLAplusVisitor } from './gen/TLAplusVisitor';

function notUndefined(value) {
  return typeof value !== 'undefined';
}

export default class TraceVisitor extends TLAplusVisitor {
  visitDef(ctx) {
    return Object.assign({}, ...super.visitDef(ctx).filter(notUndefined));
  };

  visitVariable(ctx) {
    return {
      [ctx.IDENTIFIER()] : super.visitVariable(ctx).filter(notUndefined)[0]
    };
  };

  visitValue(ctx) {
    return super.visitValue(ctx)[0];
  };

  visitTuple(ctx) {
    return super.visitTuple(ctx).filter(notUndefined);
  };

  visitMapping(ctx) {
    return Object.assign({}, ...super.visitMapping(ctx).filter(notUndefined));
  };

  visitMappingItem(ctx) {
    return {
      [ctx.IDENTIFIER()] : super.visitMappingItem(ctx)[2]
    };
  };

  visitLiteral(ctx) {
    let text = ctx.getText();
    if (ctx.BOOLEAN()) {
      return text == 'TRUE';
    } else if (ctx.NUMBER()) {
      return parseInt(text);
    } else { // string
      return text.slice(1, -1);
    }
  };
}
