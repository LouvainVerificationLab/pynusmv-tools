"""
The naive approach, with and without pre-filtering.
"""

import gc

from pynusmv.dd import BDD
from pynusmv.mc import eval_simple_expression

from ..atlkFO.ast import (TrueExp, FalseExp, Init, Reachable,
                          Atom, Not, And, Or, Implies, Iff, 
                          AF, AG, AX, AU, AW, EF, EG, EX, EU, EW,
                          nK, nE, nD, nC, K, E, D, C,
                          CEF, CEG, CEX, CEU, CEW, CAF, CAG, CAX, CAU, CAW)
from ..atlkFO.eval import (fair_states, ex, eg, eu, nk, ne, nd, nc)

from .common import *
from .utils import agents_in_list

GC_FREQUENCE = 100

def evalATLK(mas, formula, pre_filtering=False):
    """
    Return the BDD representing the set of states of mas satisfying formula.
    
    mas -- a multi-agents system;
    formula -- an AST-based ATLK formula;
    pre_filtering -- whether or not applying pre-filtering.
    """
    
    if type(formula) is TrueExp:
        return BDD.true(mas)
        
    elif type(formula) is FalseExp:
        return BDD.false(mas)
        
    elif type(formula) is Init:
        return mas.init
        
    elif type(formula) is Reachable:
        return mas.reachable_states
    
    elif type(formula) is Atom:
        return eval_simple_expression(mas, formula.value)
        
    elif type(formula) is Not:
        return ~evalATLK(mas, formula.child, pre_filtering=pre_filtering)
        
    elif type(formula) is And:
        return (evalATLK(mas, formula.left, pre_filtering=pre_filtering) &
                evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
    elif type(formula) is Or:
        return (evalATLK(mas, formula.left, pre_filtering=pre_filtering) |
                evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
    elif type(formula) is Implies:
        # a -> b = ~a | b
        return ((~evalATLK(mas, formula.left, pre_filtering=pre_filtering)) |
                evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
    elif type(formula) is Iff:
        # a <-> b = (a & b) | (~a & ~b)
        l = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        r = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        return (l & r) | ((~l) & (~r))
        
    elif type(formula) is EX:
        return ex(mas,
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is AX:
        # AX p = ~EX ~p
        return ~ex(mas,
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is EG:
        return eg(mas,
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is AG:
        # AG p = ~EF ~p = ~E[ true U ~p ]
        return ~eu(mas,
                   BDD.true(mas),
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is EU:
        return eu(mas,
                  evalATLK(mas, formula.left, pre_filtering=pre_filtering),
                  evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
    elif type(formula) is AU:
        # A[p U q] = ~E[~q W ~p & ~q] = ~(E[~q U ~p & ~q] | EG ~q)
        p = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        q = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        equpq = eu(mas, ~q, ~q & ~p)
        egq = eg(mas, ~q)
        return ~(equpq | egq)
        
    elif type(formula) is EF:
        # EF p = E[ true U p ]
        return eu(mas,
                  BDD.true(mas),
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is AF:
        # AF p = ~EG ~p
        return ~eg(mas,
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is EW:
        # E[ p W q ] = E[ p U q ] | EG p
        l = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        r = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        return eu(mas, l, r) | eg(mas, l)
        
    elif type(formula) is AW:
        # A[p W q] = ~E[~q U ~p & ~q]
        p = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        q = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        return ~eu(mas, ~q, ~p & ~q)
        
    elif type(formula) is nK:
        return nk(mas,
                  formula.agent.value,
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is K:
        # K<'a'> p = ~nK<'a'> ~p
        return ~nk(mas,
                   formula.agent.value,
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is nE:
        return ne(mas,
                  [a.value for a in formula.group],
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is E:
        # E<g> p = ~nE<g> ~p
        return ~ne(mas,
                   [a.value for a in formula.group],
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is nD:
        return nd(mas,
                  [a.value for a in formula.group],
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is D:
        # D<g> p = ~nD<g> ~p
        return ~nd(mas,
                   [a.value for a in formula.group],
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is nC:
        return nc(mas,
                  [a.value for a in formula.group],
                  evalATLK(mas, formula.child, pre_filtering=pre_filtering))
        
    elif type(formula) is C:
        # C<g> p = ~nC<g> ~p
        return ~nc(mas,
                   [a.value for a in formula.group],
                   ~evalATLK(mas, formula.child, pre_filtering=pre_filtering))
    
    elif type(formula) is CAX:
        # [g] X p = ~<g> X ~p
        new_formula = CEX(formula.group, Not(formula.child))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CAG:
        # [g] G p = ~<g> F ~p
        new_formula = CEF(formula.group, Not(formula.child))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CAU:
        # [g][p U q] = ~<g>[ ~q W ~p & ~q ]
        new_formula = CEW(formula.group,
                      Not(formula.right),
                      And(Not(formula.left), Not(formula.right)))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CAF:
        # [g] F p = ~<g> G ~p
        new_formula = CEG(formula.group, Not(formula.child))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CAW:
        # [g][p W q] = ~<g>[~q U ~p & ~q]
        new_formula = CEU(formula.group,
                      Not(formula.right),
                      And(Not(formula.left), Not(formula.right)))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CEG:
        # <g> G p = <g> p W false
        new_formula = CEW(formula.group, formula.child, FalseExp())
        return evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is CEF:
        # <g> F p = <g> true U p
        new_formula = CEU(formula.group, TrueExp(), formula.child)
        return evalATLK(mas, new_formula, pre_filtering=pre_filtering)
                   
    elif type(formula) in {CEX, CEU, CEW}:
        return eval_strat(mas, formula, pre_filtering=pre_filtering)
        
    else:
        raise Exception("evalATLK: unrecognized formula type:" + str(formula))


def eval_strat(mas, formula, pre_filtering=False):
    """
    Return the BDD representing the set of states of mas satisfying formula.
    
    mas -- a multi-agents system;
    formula -- an AST-based ATLK strategic formula;
    pre_filtering -- whether or not applying pre-filtering.
    """
    assert(type(formula) in {CEX, CEU, CEW})
    
    agents = [atom.value for atom in formula.group]
    agents = agents_in_list(mas, agents)
    
    # pre-filter if needed
    if pre_filtering:
        if type(formula) is CEX:
            sub = evalATLK(mas, formula.child, pre_filtering=pre_filtering)
            filtered = filter_cex_moves(mas, agents, sub, mas.protocol(agents))
        elif type(formula) is CEU:
            sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
            filtered = filter_ceu_moves(mas,
                                        agents,
                                        sub_1,
                                        sub_2,
                                        mas.protocol(agents))
        elif type(formula) is CEW:
            sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
            filtered = filter_cew_moves(mas,
                                        agents,
                                        sub_1,
                                        sub_2,
                                        mas.protocol(agents))
        else:
            raise Exception("eval_strat: unrecognized formula type:" +
                            str(formula))
        
        if filtered.is_false():
            return filtered
    # otherwise consider the whole protocol
    else:
        filtered = mas.protocol(agents)
    
    # split and accumulate
    nb_strats = 0
    
    sat = BDD.false(mas)
    for strat in split(mas, agents, filtered):
        if type(formula) is CEX:
            sub = evalATLK(mas, formula.child, pre_filtering=pre_filtering)
            winning = filter_cex(mas, agents, sub, strat)
        elif type(formula) is CEU:
            sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
            winning = filter_ceu(mas, agents, sub_1, sub_2, strat)
        elif type(formula) is CEW:
            sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
            winning = filter_cew(mas, agents, sub_1, sub_2, strat)
        else:
            raise Exception("eval_strat: unrecognized formula type:" +
                            str(formula))
        
        sat |= all_equiv_sat(mas, agents, winning)
        
        nb_strats += 1
        if nb_strats % GC_FREQUENCE == 0:
            gc.collect()
    
    return sat


__evalATLK_cache = {}
__orig_evalATLK = evalATLK
def __cached_evalATLK(mas, formula, pre_filtering=False):
    if (mas, formula) not in __evalATLK_cache:
        sat = __orig_evalATLK(mas, formula, pre_filtering=pre_filtering)
        __evalATLK_cache[(mas, formula)] = sat
    return __evalATLK_cache[(mas, formula)]
evalATLK = __cached_evalATLK
