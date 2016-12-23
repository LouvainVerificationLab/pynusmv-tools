"""
This module contains the class definition of the symbols and grammar of an LTL
formula
"""

import pyparsing as pp
import pynusmv_tools.bmcLTL.ast as ast

###############################################################################
# Symbols and keywords
###############################################################################

# terminals
number   = pp.Regex("[0-9]+").setParseAction(lambda s,l,t: ast.Constant(t[0]))
variable = pp.Regex("[a-zA-Z_@]+[a-zA-Z0-9_@.]*").setParseAction(lambda s,l,t: ast.Proposition(t[0]))
true     = pp.Keyword("TRUE" ).setParseAction(lambda s,l,t: ast.Constant("TRUE"))
false    = pp.Keyword("FALSE").setParseAction(lambda s,l,t: ast.Constant("FALSE"))

# temporal operators
op_G     = pp.Literal("[]")
op_F     = pp.Literal("<>")
op_X     = pp.Literal("()")
op_U     = pp.Keyword("U")
op_W     = pp.Keyword("W")

# propositional operators
op_not   = pp.Literal("!")
op_and   = pp.Literal("&")
op_or    = pp.Literal("|")
op_xor   = pp.Literal("^")
op_impl  = pp.Literal("=>")
op_iff   = pp.Literal("<=>")


# comparison
op_le    = pp.Literal("<=")
op_ge    = pp.Literal(">=")
op_lt    = pp.Literal("<")
op_gt    = pp.Literal(">")
op_eq    = pp.Literal("=")
op_neq   = pp.Literal("!=")

# arithmetic
op_lshift= pp.Literal("<<")
op_rshift= pp.Literal(">>")
op_add   = pp.Literal("+")
op_sub   = pp.Literal("-")
op_mul   = pp.Literal("*")
op_div   = pp.Literal("/")
op_mod   = pp.Literal("mod")

###############################################################################
# Parse actions used to instantiate meaningful 'nodes' of the ast.
# Note: the 'node' and the 'ast' are notions similar to but different from 
#       those in NuSMV.  
###############################################################################

# Just a map to decide based on the operator type the kind of node which needs
# to be instantiated.
factory = {
    "[]"   : ast.Globally,
    "<>"   : ast.Eventually,
    "()"   : ast.Next,
    "!"    : ast.Not,
    "U"    : ast.Until,
    "W"    : ast.WeakUntil,
    "&"    : ast.And,
    "|"    : ast.Or,
    "^"    : ast.Xor,
    "=>"   : ast.Imply,
    "<=>"  : ast.Equiv
}

def instanciate(s,l,tokens):
    """
    As the name suggests, this parse action is used to instantiate the ast node
    corresponding to some parsed expression (the tokens are passed as `tokens`)
    
    .. note::
        You should really not worry to much about the meaning of the parameters,
        there are inherited from the parseAction protocol.
        
    :param s: the original string corresponding to the text that has been parsed
    :param l: the location in the string where matching started
    :param tokens: the list of the matched tokens 
        (actually a :see:`pyparsing.ParseResult`)
    :return: the ast node (as defined in :see:`pynusmv_tools.bmcLTL.ast` corresponding 
        to the expression that has been parsed. 
    """
    members = tokens[0]
    if len(members)==2:
        return factory[members[0]](members[1])
    elif len(members) == 3:
        return factory[members[1]](members[0], members[2])
    else:
        # special case when the same binary operator is chained many times
        while len(members) > 1:
            accumulator = factory[members[1]](members[0], members[2])
            members     = [accumulator] + members[3:]
        return members[0]

def make_plain_proposition(s,l,tokens):
    """
    This parse action makes a plain Proposition (as defined in 
    :see:`pynusmv_tools.bmcLTL.ast.Proposition`) from the parsed text. 
    
    .. note::
        This action 'flattens' the expression; meaning that the result of the
        parsing of a complex proposition such as '(a + b) << 4 >= c - 6' will
        result in one single `Proposition` blob instead of being decomposed. 
        Namely, the previous example would yield::
        
            ast.Proposition( (a + b) << 4 >= c - 6 )
        
        This is a design choice motivated by the fact that:
        
            1. the objective of this tool is to illustrate the functioning of
               LTL bounded model checking and how its reduction to propositional 
               satisfiability (SAT) can be implemented with PyNuSMV as if it 
               were a brand new logical formalism; not to demonstrate how 
                relational and arithmetic expressions can be booleanized.
            2. the expressions represented this way do not contain any of the
               logical connectives which are part of LTL syntax and are as such
               out of the scope of this tool. (They can have no impact on the
               generated BMC problem).
            3. Relational and arithmetic 
               operators are only provided for the sake of being able to perform
               useful verification on realistic like models without being forced
               to go through the burden of defining DEFINE for each of the 
               expressions used.
               
    .. note::
        You should really not worry to much about the meaning of the parameters,
        there are inherited from the parseAction protocol.
        
    :param s: the original string corresponding to the text that has been parsed
    :param l: the location in the string where matching started
    :param tokens: the list of the matched tokens (actually a 
        :see:`pyparsing.ParseResult`)
    :return: a `Proposition` ast node encapsulating the parsed expression. 
    """
    members = tokens[0]
    text_of = lambda x: '('+x.id+')' if hasattr(x, 'id') else x
    members = list(map(text_of, members))
    return ast.Proposition(' '.join(members))

###############################################################################
# Grammar rules
###############################################################################

# The atoms (terminals) that may appear in a formula 
atom  = (true ^ false ^ variable ^ number)

# The arithmetic sub grammar: it implements the operators prececdence the usual 
# way. Concretely, we have:
#
# -- High precedence
#
# * unary minus
# * multiplication, division, modulus
# * addition, subtraction
# * left shift, right shift
#
# -- Low  precedence
#
arithmetic = pp.infixNotation(atom,
  [
   ((op_sub)                     , 1, pp.opAssoc.RIGHT,make_plain_proposition),
   ((op_mul    | op_div | op_mod), 2, pp.opAssoc.LEFT, make_plain_proposition),
   ((op_add    | op_sub),          2, pp.opAssoc.LEFT, make_plain_proposition),
   ((op_lshift | op_rshift),       2, pp.opAssoc.LEFT, make_plain_proposition),
  ])

# The relational sub grammar: it provides the <, <=, >, >=, = and != operators
comparison = pp.infixNotation(arithmetic,
  [
   ((op_le | op_lt | op_ge | op_gt | op_eq | op_neq), 2, pp.opAssoc.LEFT, make_plain_proposition)
  ])

# The rules to parse the LTL syntax proper and build a meaningful AST out of it.
# 
# Note: operator precedence was inspired by that descibed here:
#       http://vlsi.colorado.edu/~vis/doc/ctl_ltl/ctl_ltl/ctl_ltl.html
#
# Concretely, we have:
# -- High precedence
#
# * not, globally, eventually, next
# * and
# * or
# * xor
# * iff
# * implies
# * until
# * weak_until
#
# -- Low  precedence
#
LTL = pp.infixNotation(comparison,
  [
  ((op_not | op_X | op_F | op_G), 1, pp.opAssoc.RIGHT , instanciate),
  (op_and,  2, pp.opAssoc.LEFT  , instanciate),
  (op_or,   2, pp.opAssoc.LEFT  , instanciate),
  (op_xor,  2, pp.opAssoc.LEFT  , instanciate),
  (op_iff,  2, pp.opAssoc.LEFT  , instanciate),
  (op_impl, 2, pp.opAssoc.LEFT  , instanciate),
  (op_U,    2, pp.opAssoc.LEFT  , instanciate),
  (op_W,    2, pp.opAssoc.LEFT  , instanciate)
  ])
 
def parseLTL(text):
    """
    Parses an LTL string and returns the corresponding AST
     
    :param text: the text to be parsed
    :return: an LTL ast corresponding to the parsed LTL expression
    """
    return LTL.parseString(text)[0]
