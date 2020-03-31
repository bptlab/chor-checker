import { TLAplusVisitor } from './gen/TLAplusVisitor';

function notUndefined(value) {
  return typeof value !== 'undefined';
}

/**
 * Visitor for the AST output of the TLAplus state trace parser.
 * Generates a JSON representation of the state, e.g., mappings
 * are converted to objects and tuples to arrays.
 */
export default class TraceVisitor extends TLAplusVisitor {
  visitDef(ctx) {
    // definitions are a set of variables that can merged into one object
    return Object.assign({}, ...super.visitDef(ctx).filter(notUndefined));
  };

  visitVariable(ctx) {
    // map variables to an object containing a single 'key -> value' pair
    return {
      [ctx.IDENTIFIER()] : super.visitVariable(ctx).filter(notUndefined)[0]
    };
  };

  visitValue(ctx) {
    // values can be tuples, mappings, or literals, thus we just pass through
    return super.visitValue(ctx)[0];
  };

  visitTuple(ctx) {
    // a tuple gets mapped to an array of values implicitly
    return super.visitTuple(ctx).filter(notUndefined);
  };

  visitSet(ctx) {
    // a sets gets mapped to an array of values implicitly
    return super.visitSet(ctx).filter(notUndefined);
  };

  visitMapping(ctx) {
    // a mapping is a set of mapping items which get merged into one object
    return Object.assign({}, ...super.visitMapping(ctx).filter(notUndefined));
  };

  visitMappingItem(ctx) {
    // a mapping item is a single object containing a 'key -> value' pair
    return {
      [ctx.IDENTIFIER()] : super.visitMappingItem(ctx)[2]
    };
  };

  visitLiteral(ctx) {
    // literals are the leaves in the tree and get mapped to their literal value
    let text = ctx.getText();
    if (ctx.BOOLEAN()) {
      // boolean, convert to native bool
      return text == 'TRUE';
    } else if (ctx.NUMBER()) {
      // number, we only support integers
      return parseInt(text);
    } else {
      // string, slice "quotes"
      return text.slice(1, -1);
    }
  };
}
