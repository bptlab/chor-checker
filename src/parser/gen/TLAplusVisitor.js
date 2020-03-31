// Generated from TLAplus.antlr by ANTLR 4.8
// jshint ignore: start
var antlr4 = require('antlr4/index');

// This class defines a complete generic visitor for a parse tree produced by TLAplusParser.

function TLAplusVisitor() {
	antlr4.tree.ParseTreeVisitor.call(this);
	return this;
}

TLAplusVisitor.prototype = Object.create(antlr4.tree.ParseTreeVisitor.prototype);
TLAplusVisitor.prototype.constructor = TLAplusVisitor;

// Visit a parse tree produced by TLAplusParser#def.
TLAplusVisitor.prototype.visitDef = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#variable.
TLAplusVisitor.prototype.visitVariable = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#value.
TLAplusVisitor.prototype.visitValue = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#tuple.
TLAplusVisitor.prototype.visitTuple = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#mapping.
TLAplusVisitor.prototype.visitMapping = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#mappingItem.
TLAplusVisitor.prototype.visitMappingItem = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#set.
TLAplusVisitor.prototype.visitSet = function(ctx) {
  return this.visitChildren(ctx);
};


// Visit a parse tree produced by TLAplusParser#literal.
TLAplusVisitor.prototype.visitLiteral = function(ctx) {
  return this.visitChildren(ctx);
};



exports.TLAplusVisitor = TLAplusVisitor;