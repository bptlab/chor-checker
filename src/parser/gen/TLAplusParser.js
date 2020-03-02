// Generated from TLAplus.antlr by ANTLR 4.8
// jshint ignore: start
var antlr4 = require('antlr4/index');
var TLAplusVisitor = require('./TLAplusVisitor').TLAplusVisitor;

var grammarFileName = "TLAplus.antlr";


var serializedATN = ["\u0003\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964",
    "\u0003\u000f@\u0004\u0002\t\u0002\u0004\u0003\t\u0003\u0004\u0004\t",
    "\u0004\u0004\u0005\t\u0005\u0004\u0006\t\u0006\u0004\u0007\t\u0007\u0004",
    "\b\t\b\u0003\u0002\u0003\u0002\u0006\u0002\u0013\n\u0002\r\u0002\u000e",
    "\u0002\u0014\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0003\u0004",
    "\u0003\u0004\u0003\u0004\u0005\u0004\u001e\n\u0004\u0003\u0005\u0003",
    "\u0005\u0003\u0005\u0003\u0005\u0007\u0005$\n\u0005\f\u0005\u000e\u0005",
    "\'\u000b\u0005\u0005\u0005)\n\u0005\u0003\u0005\u0003\u0005\u0003\u0006",
    "\u0003\u0006\u0003\u0006\u0003\u0006\u0007\u00061\n\u0006\f\u0006\u000e",
    "\u00064\u000b\u0006\u0005\u00066\n\u0006\u0003\u0006\u0003\u0006\u0003",
    "\u0007\u0003\u0007\u0003\u0007\u0003\u0007\u0003\b\u0003\b\u0003\b\u0002",
    "\u0002\t\u0002\u0004\u0006\b\n\f\u000e\u0002\u0003\u0003\u0002\u0003",
    "\u0005\u0002?\u0002\u0012\u0003\u0002\u0002\u0002\u0004\u0016\u0003",
    "\u0002\u0002\u0002\u0006\u001d\u0003\u0002\u0002\u0002\b\u001f\u0003",
    "\u0002\u0002\u0002\n,\u0003\u0002\u0002\u0002\f9\u0003\u0002\u0002\u0002",
    "\u000e=\u0003\u0002\u0002\u0002\u0010\u0011\u0007\t\u0002\u0002\u0011",
    "\u0013\u0005\u0004\u0003\u0002\u0012\u0010\u0003\u0002\u0002\u0002\u0013",
    "\u0014\u0003\u0002\u0002\u0002\u0014\u0012\u0003\u0002\u0002\u0002\u0014",
    "\u0015\u0003\u0002\u0002\u0002\u0015\u0003\u0003\u0002\u0002\u0002\u0016",
    "\u0017\u0007\u0006\u0002\u0002\u0017\u0018\u0007\b\u0002\u0002\u0018",
    "\u0019\u0005\u0006\u0004\u0002\u0019\u0005\u0003\u0002\u0002\u0002\u001a",
    "\u001e\u0005\b\u0005\u0002\u001b\u001e\u0005\n\u0006\u0002\u001c\u001e",
    "\u0005\u000e\b\u0002\u001d\u001a\u0003\u0002\u0002\u0002\u001d\u001b",
    "\u0003\u0002\u0002\u0002\u001d\u001c\u0003\u0002\u0002\u0002\u001e\u0007",
    "\u0003\u0002\u0002\u0002\u001f(\u0007\u000b\u0002\u0002 %\u0005\u0006",
    "\u0004\u0002!\"\u0007\n\u0002\u0002\"$\u0005\u0006\u0004\u0002#!\u0003",
    "\u0002\u0002\u0002$\'\u0003\u0002\u0002\u0002%#\u0003\u0002\u0002\u0002",
    "%&\u0003\u0002\u0002\u0002&)\u0003\u0002\u0002\u0002\'%\u0003\u0002",
    "\u0002\u0002( \u0003\u0002\u0002\u0002()\u0003\u0002\u0002\u0002)*\u0003",
    "\u0002\u0002\u0002*+\u0007\f\u0002\u0002+\t\u0003\u0002\u0002\u0002",
    ",5\u0007\r\u0002\u0002-2\u0005\f\u0007\u0002./\u0007\n\u0002\u0002/",
    "1\u0005\f\u0007\u00020.\u0003\u0002\u0002\u000214\u0003\u0002\u0002",
    "\u000220\u0003\u0002\u0002\u000223\u0003\u0002\u0002\u000236\u0003\u0002",
    "\u0002\u000242\u0003\u0002\u0002\u00025-\u0003\u0002\u0002\u000256\u0003",
    "\u0002\u0002\u000267\u0003\u0002\u0002\u000278\u0007\u000e\u0002\u0002",
    "8\u000b\u0003\u0002\u0002\u00029:\u0007\u0006\u0002\u0002:;\u0007\u0007",
    "\u0002\u0002;<\u0005\u0006\u0004\u0002<\r\u0003\u0002\u0002\u0002=>",
    "\t\u0002\u0002\u0002>\u000f\u0003\u0002\u0002\u0002\b\u0014\u001d%(",
    "25"].join("");


var atn = new antlr4.atn.ATNDeserializer().deserialize(serializedATN);

var decisionsToDFA = atn.decisionToState.map( function(ds, index) { return new antlr4.dfa.DFA(ds, index); });

var sharedContextCache = new antlr4.PredictionContextCache();

var literalNames = [ null, null, null, null, null, "'|->'", "'='", "'/\\'", 
                     "','", "'<<'", "'>>'", "'['", "']'" ];

var symbolicNames = [ null, "BOOLEAN", "STRING", "NUMBER", "IDENTIFIER", 
                      "MAPS_TO", "EQUALS", "AND", "COMMA", "TUPLE_OPEN", 
                      "TUPLE_CLOSE", "MAPPING_OPEN", "MAPPING_CLOSE", "WS" ];

var ruleNames =  [ "def", "variable", "value", "tuple", "mapping", "mappingItem", 
                   "literal" ];

function TLAplusParser (input) {
	antlr4.Parser.call(this, input);
    this._interp = new antlr4.atn.ParserATNSimulator(this, atn, decisionsToDFA, sharedContextCache);
    this.ruleNames = ruleNames;
    this.literalNames = literalNames;
    this.symbolicNames = symbolicNames;
    return this;
}

TLAplusParser.prototype = Object.create(antlr4.Parser.prototype);
TLAplusParser.prototype.constructor = TLAplusParser;

Object.defineProperty(TLAplusParser.prototype, "atn", {
	get : function() {
		return atn;
	}
});

TLAplusParser.EOF = antlr4.Token.EOF;
TLAplusParser.BOOLEAN = 1;
TLAplusParser.STRING = 2;
TLAplusParser.NUMBER = 3;
TLAplusParser.IDENTIFIER = 4;
TLAplusParser.MAPS_TO = 5;
TLAplusParser.EQUALS = 6;
TLAplusParser.AND = 7;
TLAplusParser.COMMA = 8;
TLAplusParser.TUPLE_OPEN = 9;
TLAplusParser.TUPLE_CLOSE = 10;
TLAplusParser.MAPPING_OPEN = 11;
TLAplusParser.MAPPING_CLOSE = 12;
TLAplusParser.WS = 13;

TLAplusParser.RULE_def = 0;
TLAplusParser.RULE_variable = 1;
TLAplusParser.RULE_value = 2;
TLAplusParser.RULE_tuple = 3;
TLAplusParser.RULE_mapping = 4;
TLAplusParser.RULE_mappingItem = 5;
TLAplusParser.RULE_literal = 6;


function DefContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_def;
    return this;
}

DefContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
DefContext.prototype.constructor = DefContext;

DefContext.prototype.AND = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(TLAplusParser.AND);
    } else {
        return this.getToken(TLAplusParser.AND, i);
    }
};


DefContext.prototype.variable = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(VariableContext);
    } else {
        return this.getTypedRuleContext(VariableContext,i);
    }
};

DefContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitDef(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.DefContext = DefContext;

TLAplusParser.prototype.def = function() {

    var localctx = new DefContext(this, this._ctx, this.state);
    this.enterRule(localctx, 0, TLAplusParser.RULE_def);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 16; 
        this._errHandler.sync(this);
        _la = this._input.LA(1);
        do {
            this.state = 14;
            this.match(TLAplusParser.AND);
            this.state = 15;
            this.variable();
            this.state = 18; 
            this._errHandler.sync(this);
            _la = this._input.LA(1);
        } while(_la===TLAplusParser.AND);
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function VariableContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_variable;
    return this;
}

VariableContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
VariableContext.prototype.constructor = VariableContext;

VariableContext.prototype.IDENTIFIER = function() {
    return this.getToken(TLAplusParser.IDENTIFIER, 0);
};

VariableContext.prototype.EQUALS = function() {
    return this.getToken(TLAplusParser.EQUALS, 0);
};

VariableContext.prototype.value = function() {
    return this.getTypedRuleContext(ValueContext,0);
};

VariableContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitVariable(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.VariableContext = VariableContext;

TLAplusParser.prototype.variable = function() {

    var localctx = new VariableContext(this, this._ctx, this.state);
    this.enterRule(localctx, 2, TLAplusParser.RULE_variable);
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 20;
        this.match(TLAplusParser.IDENTIFIER);
        this.state = 21;
        this.match(TLAplusParser.EQUALS);
        this.state = 22;
        this.value();
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function ValueContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_value;
    return this;
}

ValueContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
ValueContext.prototype.constructor = ValueContext;

ValueContext.prototype.tuple = function() {
    return this.getTypedRuleContext(TupleContext,0);
};

ValueContext.prototype.mapping = function() {
    return this.getTypedRuleContext(MappingContext,0);
};

ValueContext.prototype.literal = function() {
    return this.getTypedRuleContext(LiteralContext,0);
};

ValueContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitValue(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.ValueContext = ValueContext;

TLAplusParser.prototype.value = function() {

    var localctx = new ValueContext(this, this._ctx, this.state);
    this.enterRule(localctx, 4, TLAplusParser.RULE_value);
    try {
        this.state = 27;
        this._errHandler.sync(this);
        switch(this._input.LA(1)) {
        case TLAplusParser.TUPLE_OPEN:
            this.enterOuterAlt(localctx, 1);
            this.state = 24;
            this.tuple();
            break;
        case TLAplusParser.MAPPING_OPEN:
            this.enterOuterAlt(localctx, 2);
            this.state = 25;
            this.mapping();
            break;
        case TLAplusParser.BOOLEAN:
        case TLAplusParser.STRING:
        case TLAplusParser.NUMBER:
            this.enterOuterAlt(localctx, 3);
            this.state = 26;
            this.literal();
            break;
        default:
            throw new antlr4.error.NoViableAltException(this);
        }
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function TupleContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_tuple;
    return this;
}

TupleContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
TupleContext.prototype.constructor = TupleContext;

TupleContext.prototype.TUPLE_OPEN = function() {
    return this.getToken(TLAplusParser.TUPLE_OPEN, 0);
};

TupleContext.prototype.TUPLE_CLOSE = function() {
    return this.getToken(TLAplusParser.TUPLE_CLOSE, 0);
};

TupleContext.prototype.value = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(ValueContext);
    } else {
        return this.getTypedRuleContext(ValueContext,i);
    }
};

TupleContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(TLAplusParser.COMMA);
    } else {
        return this.getToken(TLAplusParser.COMMA, i);
    }
};


TupleContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitTuple(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.TupleContext = TupleContext;

TLAplusParser.prototype.tuple = function() {

    var localctx = new TupleContext(this, this._ctx, this.state);
    this.enterRule(localctx, 6, TLAplusParser.RULE_tuple);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 29;
        this.match(TLAplusParser.TUPLE_OPEN);
        this.state = 38;
        this._errHandler.sync(this);
        _la = this._input.LA(1);
        if((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << TLAplusParser.BOOLEAN) | (1 << TLAplusParser.STRING) | (1 << TLAplusParser.NUMBER) | (1 << TLAplusParser.TUPLE_OPEN) | (1 << TLAplusParser.MAPPING_OPEN))) !== 0)) {
            this.state = 30;
            this.value();
            this.state = 35;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===TLAplusParser.COMMA) {
                this.state = 31;
                this.match(TLAplusParser.COMMA);
                this.state = 32;
                this.value();
                this.state = 37;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
        }

        this.state = 40;
        this.match(TLAplusParser.TUPLE_CLOSE);
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function MappingContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_mapping;
    return this;
}

MappingContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
MappingContext.prototype.constructor = MappingContext;

MappingContext.prototype.MAPPING_OPEN = function() {
    return this.getToken(TLAplusParser.MAPPING_OPEN, 0);
};

MappingContext.prototype.MAPPING_CLOSE = function() {
    return this.getToken(TLAplusParser.MAPPING_CLOSE, 0);
};

MappingContext.prototype.mappingItem = function(i) {
    if(i===undefined) {
        i = null;
    }
    if(i===null) {
        return this.getTypedRuleContexts(MappingItemContext);
    } else {
        return this.getTypedRuleContext(MappingItemContext,i);
    }
};

MappingContext.prototype.COMMA = function(i) {
	if(i===undefined) {
		i = null;
	}
    if(i===null) {
        return this.getTokens(TLAplusParser.COMMA);
    } else {
        return this.getToken(TLAplusParser.COMMA, i);
    }
};


MappingContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitMapping(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.MappingContext = MappingContext;

TLAplusParser.prototype.mapping = function() {

    var localctx = new MappingContext(this, this._ctx, this.state);
    this.enterRule(localctx, 8, TLAplusParser.RULE_mapping);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 42;
        this.match(TLAplusParser.MAPPING_OPEN);
        this.state = 51;
        this._errHandler.sync(this);
        _la = this._input.LA(1);
        if(_la===TLAplusParser.IDENTIFIER) {
            this.state = 43;
            this.mappingItem();
            this.state = 48;
            this._errHandler.sync(this);
            _la = this._input.LA(1);
            while(_la===TLAplusParser.COMMA) {
                this.state = 44;
                this.match(TLAplusParser.COMMA);
                this.state = 45;
                this.mappingItem();
                this.state = 50;
                this._errHandler.sync(this);
                _la = this._input.LA(1);
            }
        }

        this.state = 53;
        this.match(TLAplusParser.MAPPING_CLOSE);
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function MappingItemContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_mappingItem;
    return this;
}

MappingItemContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
MappingItemContext.prototype.constructor = MappingItemContext;

MappingItemContext.prototype.IDENTIFIER = function() {
    return this.getToken(TLAplusParser.IDENTIFIER, 0);
};

MappingItemContext.prototype.MAPS_TO = function() {
    return this.getToken(TLAplusParser.MAPS_TO, 0);
};

MappingItemContext.prototype.value = function() {
    return this.getTypedRuleContext(ValueContext,0);
};

MappingItemContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitMappingItem(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.MappingItemContext = MappingItemContext;

TLAplusParser.prototype.mappingItem = function() {

    var localctx = new MappingItemContext(this, this._ctx, this.state);
    this.enterRule(localctx, 10, TLAplusParser.RULE_mappingItem);
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 55;
        this.match(TLAplusParser.IDENTIFIER);
        this.state = 56;
        this.match(TLAplusParser.MAPS_TO);
        this.state = 57;
        this.value();
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


function LiteralContext(parser, parent, invokingState) {
	if(parent===undefined) {
	    parent = null;
	}
	if(invokingState===undefined || invokingState===null) {
		invokingState = -1;
	}
	antlr4.ParserRuleContext.call(this, parent, invokingState);
    this.parser = parser;
    this.ruleIndex = TLAplusParser.RULE_literal;
    return this;
}

LiteralContext.prototype = Object.create(antlr4.ParserRuleContext.prototype);
LiteralContext.prototype.constructor = LiteralContext;

LiteralContext.prototype.NUMBER = function() {
    return this.getToken(TLAplusParser.NUMBER, 0);
};

LiteralContext.prototype.STRING = function() {
    return this.getToken(TLAplusParser.STRING, 0);
};

LiteralContext.prototype.BOOLEAN = function() {
    return this.getToken(TLAplusParser.BOOLEAN, 0);
};

LiteralContext.prototype.accept = function(visitor) {
    if ( visitor instanceof TLAplusVisitor ) {
        return visitor.visitLiteral(this);
    } else {
        return visitor.visitChildren(this);
    }
};




TLAplusParser.LiteralContext = LiteralContext;

TLAplusParser.prototype.literal = function() {

    var localctx = new LiteralContext(this, this._ctx, this.state);
    this.enterRule(localctx, 12, TLAplusParser.RULE_literal);
    var _la = 0; // Token type
    try {
        this.enterOuterAlt(localctx, 1);
        this.state = 59;
        _la = this._input.LA(1);
        if(!((((_la) & ~0x1f) == 0 && ((1 << _la) & ((1 << TLAplusParser.BOOLEAN) | (1 << TLAplusParser.STRING) | (1 << TLAplusParser.NUMBER))) !== 0))) {
        this._errHandler.recoverInline(this);
        }
        else {
        	this._errHandler.reportMatch(this);
            this.consume();
        }
    } catch (re) {
    	if(re instanceof antlr4.error.RecognitionException) {
	        localctx.exception = re;
	        this._errHandler.reportError(this, re);
	        this._errHandler.recover(this, re);
	    } else {
	    	throw re;
	    }
    } finally {
        this.exitRule();
    }
    return localctx;
};


exports.TLAplusParser = TLAplusParser;
