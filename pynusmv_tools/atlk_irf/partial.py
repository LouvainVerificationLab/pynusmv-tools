"""
The partial approach, with and without pre-filtering.
"""

import gc

from pynusmv.dd import BDD
from pynusmv.mc import eval_simple_expression
from pynusmv.utils import fixpoint

from ..atlkFO.ast import (TrueExp, FalseExp, Init, Reachable,
                          Atom, Not, And, Or, Implies, Iff, 
                          AF, AG, AX, AU, AW, EF, EG, EX, EU, EW,
                          nK, nE, nD, nC, K, E, D, C,
                          CEF, CEG, CEX, CEU, CEW, CAF, CAG, CAX, CAU, CAW)
from ..atlkFO.eval import (fair_states, ex, eg, eu, nk, ne, nd, nc)

from .common import *
from .utils import *

GC_FREQUENCE = 100

def evalATLK(mas, formula, states=None, pre_filtering=False):
    """
    Return the BDD representing the subset of the given states of mas
    satisfying formula.
    
    mas -- a multi-agents system;
    formula -- an AST-based ATLK formula;
    states -- if not None, a subset of states of mas;
              if None, the initial states are used instead;
    pre_filtering -- whether or not applying pre-filtering.
    """
    
    if states is None:
        states = mas.init
    
    if type(formula) is TrueExp:
        return states
        
    elif type(formula) is FalseExp:
        return BDD.false(mas)
        
    elif type(formula) is Init:
        return mas.init & states
        
    elif type(formula) is Reachable:
        return mas.reachable_states & states
    
    elif type(formula) is Atom:
        return eval_simple_expression(mas, formula.value) & states
        
    elif type(formula) is Not:
        return states - evalATLK(mas,
                                 formula.child,
                                 states=states,
                                 pre_filtering=pre_filtering)
        
    elif type(formula) is And:
        return (evalATLK(mas,
                         formula.left,
                         states=states,
                         pre_filtering=pre_filtering) &
                evalATLK(mas,
                         formula.right,
                         states=states,
                         pre_filtering=pre_filtering))
        
    elif type(formula) is Or:
        return (evalATLK(mas,
                         formula.left,
                         states=states,
                         pre_filtering=pre_filtering) |
                evalATLK(mas,
                         formula.right,
                         states=states,
                         pre_filtering=pre_filtering))
        
    elif type(formula) is Implies:
        # a -> b = ~a | b
        p = formula.left
        q = formula.right
        new_formula = Or(Not(p), q)
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is Iff:
        # a <-> b = (a & b) | (~a & ~b)
        p = formula.left
        q = formula.right
        new_formula = Or(And(p, q), And(Not(p), Not(q)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is EX:
        return ex(mas,
                  evalATLK(mas,
                           formula.child,
                           states=mas.post(states),
                           pre_filtering=pre_filtering)) & states
        
    elif type(formula) is AX:
        # AX p = ~EX ~p
        new_formula = Not(EX(Not(spec.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is EG:
        return eg(mas,
                  evalATLK(mas,
                           formula.child,
                           states=reach(mas, states),
                           pre_filtering=pre_filtering)) & states
        
    elif type(formula) is AG:
        # AG p = ~EF ~p = ~E[ true U ~p ]
        new_formula = Not(EF(Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is EU:
        return eu(mas,
                  evalATLK(mas,
                           formula.left,
                           states=reach(mas, states),
                           pre_filtering=pre_filtering),
                  evalATLK(mas,
                           formula.right,
                           states=reach(mas, states),
                           pre_filtering=pre_filtering))
        
    elif type(formula) is AU:
        # A[p U q] = ~E[~q W ~p & ~q] = ~(E[~q U ~p & ~q] | EG ~q)
        p = formula.left
        q = formula.right
        new_formula = Not(Or(EU(Not(q), And(Not(p), Not(q))), EG(Not(q))))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is EF:
        # EF p = E[ true U p ]
        new_formula = EU(TrueExp(), formula.child)
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is AF:
        # AF p = ~EG ~p
        new_formula = Not(EG(Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is EW:
        # E[ p W q ] = E[ p U q ] | EG p
        p = formula.left
        q = formula.right
        new_formula = Or(EU(p, q), EG(p))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is AW:
        # A[p W q] = ~E[~q U ~p & ~q]
        p = formula.left
        q = formula.right
        new_formula = Not(EU(Not(q), And(Not(p), Not(q))))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is nK:
        agent = [formula.agent.value]
        phi = evalATLK(mas,
                       formula.child,
                       states=mas.equivalent_states(states, agent) &
                              mas.reachable_states,
                       pre_filtering=pre_filtering)
        return nk(mas,
                  formula.agent.value,
                  phi) & states
        
    elif type(formula) is K:
        # K<'a'> p = ~nK<'a'> ~p
        new_formula = Not(nK(formula.agent, Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is nE:
        agents = [a.value for a in formula.group]
        equiv = Eequiv(mas, agents, states)
        phi = evalATLK(mas,
                       formula.child,
                       states=equiv,
                       pre_filtering=pre_filtering)
        return ne(mas, agents, phi) & states
        
    elif type(formula) is E:
        # E<g> p = ~nE<g> ~p
        new_formula = Not(nE(formula.group, Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is nD:
        agents = [a.value for a in formula.group]
        equiv = Dequiv(mas, agents, states)
        phi = evalATLK(mas,
                       formula.child,
                       states=equiv,
                       pre_filtering=pre_filtering)
        return nd(mas, agents, phi) & states
        
    elif type(formula) is D:
        # D<g> p = ~nD<g> ~p
        new_formula = Not(nD(formula.group, Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is nC:
        agents = [a.value for a in formula.group]
        equiv = Cequiv(mas, agents, states)
        phi = evalATLK(mas,
                       formula.child,
                       states=equiv,
                       pre_filtering=pre_filtering)
        return nd(mas, agents, phi) & states
        
    elif type(formula) is C:
        # C<g> p = ~nC<g> ~p
        new_formula = Not(nC(formula.group, Not(formula.child)))
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
    
    elif type(formula) is CAX:
        # [g] X p = ~<g> X ~p
        new_formula = CEX(formula.group, Not(formula.child))
        return ~evalATLK(mas,
                         new_formula,
                         states=states,
                         pre_filtering=pre_filtering)
        
    elif type(formula) is CAG:
        # [g] G p = ~<g> F ~p
        new_formula = CEF(formula.group, Not(formula.child))
        return ~evalATLK(mas,
                         new_formula,
                         states=states,
                         pre_filtering=pre_filtering)
        
    elif type(formula) is CAU:
        # [g][p U q] = ~<g>[ ~q W ~p & ~q ]
        new_formula = CEW(formula.group,
                      Not(formula.right),
                      And(Not(formula.left), Not(formula.right)))
        return ~evalATLK(mas,
                         new_formula,
                         states=states,
                         pre_filtering=pre_filtering)
        
    elif type(formula) is CAF:
        # [g] F p = ~<g> G ~p
        new_formula = CEG(formula.group, Not(formula.child))
        return ~evalATLK(mas,
                         new_formula,
                         states=states,
                         pre_filtering=pre_filtering)
        
    elif type(formula) is CAW:
        # [g][p W q] = ~<g>[~q U ~p & ~q]
        new_formula = CEU(formula.group,
                      Not(formula.right),
                      And(Not(formula.left), Not(formula.right)))
        return ~evalATLK(mas,
                         new_formula,
                         states=states,
                         pre_filtering=pre_filtering)
        
    elif type(formula) is CEG:
        # <g> G p = <g> p W false
        new_formula = CEW(formula.group, formula.child, FalseExp())
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is CEF:
        # <g> F p = <g> true U p
        new_formula = CEU(formula.group, TrueExp(), formula.child)
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
                   
    elif type(formula) in {CEX, CEU, CEW}:
        return eval_strat(mas,
                          formula,
                          states,
                          pre_filtering=pre_filtering)
        
    else:
        raise Exception("evalATLK: unrecognized formula type:" + str(formula))


def eval_strat(mas, formula, states, pre_filtering=False):
    """
    Return the BDD representing the subset of the given states of mas
    satisfying formula.
    
    mas -- a multi-agents system;
    formula -- an AST-based ATLK strategic formula;
    states -- a subset of states of mas;
    pre_filtering -- whether or not applying pre-filtering.
    """
    assert(type(formula) in {CEX, CEU, CEW})
    
    agents = [atom.value for atom in formula.group]
    agents = agents_in_list(mas, agents)
    
    # pre-filter if needed
    if pre_filtering:
        if type(formula) is CEX:
            sub_states = post_through(mas,
                                      agents,
                                      Eequiv(mas, agents, states),
                                      mas.protocol(agents))
            sub = evalATLK(mas,
                           formula.child,
                           states=sub_states,
                           pre_filtering=pre_filtering)
            filtered = filter_cex_moves(mas, agents, sub, mas.protocol(agents))
        elif type(formula) is CEU:
            sub_1 = evalATLK(mas,
                             formula.left,
                             states=reach(mas, states),
                             pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas,
                             formula.right,
                             states=reach(mas, states),
                             pre_filtering=pre_filtering)
            filtered = filter_ceu_moves(mas,
                                        agents,
                                        sub_1,
                                        sub_2,
                                        mas.protocol(agents))
        elif type(formula) is CEW:
            sub_1 = evalATLK(mas,
                             formula.left,
                             states=reach(mas, states),
                             pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas,
                             formula.right,
                             states=reach(mas, states),
                             pre_filtering=pre_filtering)
            filtered = filter_cew_moves(mas,
                                        agents,
                                        sub_1,
                                        sub_2,
                                        mas.protocol(agents))
        else:
            raise Exception("eval_strat: unrecognized formula type:" +
                            str(formula))
        
        if (states & filtered).is_false():
            return BDD.false(mas)
    # otherwise consider the whole protocol
    else:
        filtered = mas.protocol(agents)
    
    # Remove states for which we already know there are no possible strategies
    states = (states & filtered).forsome(mas.bddEnc.inputsCube)
    
    # split and accumulate
    nb_strats = 0
    
    sat = BDD.false(mas)
    for strat in partial_strategies_filtered(mas,
                                             agents,
                                             Eequiv(mas, agents, states),
                                             filtered):
        if sat == states:
            return sat
        
        if type(formula) is CEX:
            sub_states = post_through(mas,
                                      agents,
                                      Eequiv(mas, agents, states),
                                      strat)
            sub = evalATLK(mas,
                           formula.child,
                           states=sub_states,
                           pre_filtering=pre_filtering)
            winning = filter_cex(mas, agents, sub, strat)
        elif type(formula) is CEU:
            sub_1 = evalATLK(mas,
                             formula.left,
                             states=strat.forsome(mas.bddEnc.inputsCube),
                             pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas,
                             formula.right,
                             states=strat.forsome(mas.bddEnc.inputsCube),
                             pre_filtering=pre_filtering)
            winning = filter_ceu(mas, agents, sub_1, sub_2, strat)
        elif type(formula) is CEW:
            sub_1 = evalATLK(mas,
                             formula.left,
                             states=strat.forsome(mas.bddEnc.inputsCube),
                             pre_filtering=pre_filtering)
            sub_2 = evalATLK(mas,
                             formula.right,
                             states=strat.forsome(mas.bddEnc.inputsCube),
                             pre_filtering=pre_filtering)
            winning = filter_cew(mas, agents, sub_1, sub_2, strat)
        else:
            raise Exception("eval_strat: unrecognized formula type:" +
                            str(formula))
        
        sat |= all_equiv_sat(mas, agents, winning) & states
        
        nb_strats += 1
        if nb_strats % GC_FREQUENCE == 0:
            gc.collect()
    
    return sat


def reach_split_filtered(mas, agents, moves, filtered):
    """
    Return the set of largest non-agents-conflicting extensions of the given
    set of moves with moves of filtered reachable from moves.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    moves -- a subset of moves for agents;
    filtered -- a subset of moves for agents.
    """
    new_states = (post_through(mas, agents, BDD.true(mas), moves) -
                  moves.forsome(mas.bddEnc.inputsCube))
    new_moves = new_states & filtered
    compatible = compatible_moves(mas, agents, new_moves, moves)
    if compatible.is_false():
        yield moves
    else:
        for sub_strat in split(mas, agents, compatible):
            for new_strat in reach_split_filtered(mas,
                                                  agents,
                                                  moves | sub_strat,
                                                  filtered):
                yield new_strat


def partial_strategies_filtered(mas, agents, states, filtered):
    """
    Return the set of non-agents-conflicting subsets of filtered reachable from
    some of the given states in mas.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    states -- a subset of states of mas;
    filtered -- a subset of moves for agents.
    """
    for nc_moves in split(mas, agents, states & filtered):
        for strat in reach_split_filtered(mas, agents, nc_moves, filtered):
            yield strat


# ----- caching ---------------------------------------------------------------

__evalATLK_cache = {}
__orig_evalATLK = evalATLK
def __cached_evalATLK(mas, formula, states=None, pre_filtering=False):
    if states is None:
        states = mas.init
    
    if (mas, formula) in __evalATLK_cache.keys():
        sat, unsat = __evalATLK_cache[(mas, formula)]
    else:
        false = BDD.false(mas)
        sat, unsat = false, false
    
    remaining = states - (sat | unsat)
    
    if remaining.isnot_false():
        remsat = __orig_evalATLK(mas,
                                 formula,
                                 states=remaining,
                                 pre_filtering=pre_filtering)
        remunsat = remaining - remsat
        __evalATLK_cache[(mas, formula)] = (sat + remsat, unsat + remunsat)
    else:
        remsat = BDD.false(mas)
    
    return sat + remsat

evalATLK = __cached_evalATLK
