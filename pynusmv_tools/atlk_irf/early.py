"""
The early approach, with and without pre-filtering.
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


nb_strats = 0

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
    
    equiv_states = Eequiv(mas, agents, states)
    
    # pre-filter if needed
    if pre_filtering:
        if type(formula) is CEX:
            sub_states = post_through(mas,
                                      agents,
                                      equiv_states,
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
        
        if (equiv_states & filtered).is_false():
            return BDD.false(mas)
    # otherwise consider the whole protocol
    else:
        filtered = mas.protocol(agents)
    
    # Remove states for which we already know there are no possible strategies
    equiv_states = (equiv_states & filtered).forsome(mas.bddEnc.inputsCube)
    
    # Iterate over partial strategies starting in equiv_states
    global nb_strats
    nb_strats = 0
    
    sat = BDD.false(mas)
    for strat in split(mas, agents, equiv_states & filtered):
        win = eval_alt(mas,
                       formula,
                       agents,
                       equiv_states,
                       strat,
                       filtered,
                       pre_filtering=pre_filtering)
        sat |= (win & states)
        equiv_states -= win
        if equiv_states.is_false():
            break
    return sat


def complete_compatible(mas, agents, moves):
    """
    Return the given moves extended with the set of moves reachable from these
    ones and compatible with them.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    moves -- a set of non-agents-conflicting moves.
    """
    result = moves
    new_states = (post_through(mas, agents, BDD.true(mas), result) -
                  result.forsome(mas.bddEnc.inputsCube))
    new_moves = compatible_moves(mas,
                                 agents,
                                 new_states & mas.protocol(agents),
                                 moves)
    while new_moves.isnot_false():
        result = result | new_moves
        new_states = (post_through(mas, agents, BDD.true(mas), result) -
                      result.forsome(mas.bddEnc.inputsCube))
        new_moves = compatible_moves(mas,
                                     agents,
                                     new_states & mas.protocol(agents),
                                     moves)
    return result


def eval_alt(mas,
             formula,
             agents,
             states,
             strat,
             filtered,
             pre_filtering=False):
    """
    Return the subset of states for which there exists an extension of strat
    with moves of filtered winning for formula.
    """
    global nb_strats
    nb_strats += 1
    if nb_strats % GC_FREQUENCE == 0:
        gc.collect()
    
    # Complete the strategy
    completed_strat = complete_compatible(mas, agents, strat)
    
    # strategic filtering
    if type(formula) is CEX:
        sub_states = post_through(mas,
                                  agents,
                                  Eequiv(mas, agents, states),
                                  completed_strat)
        sub = evalATLK(mas,
                       formula.child,
                       states=sub_states,
                       pre_filtering=pre_filtering)
        notlose = filter_cex(mas, agents, sub, completed_strat) & states
    elif type(formula) is CEU:
        sub_1 = evalATLK(mas,
                         formula.left,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas,
                         formula.right,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        notlose = filter_ceu(mas,
                             agents,
                             sub_1,
                             sub_2,
                             completed_strat) & states
    elif type(formula) is CEW:
        sub_1 = evalATLK(mas,
                         formula.left,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas,
                         formula.right,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        notlose = filter_cew(mas,
                             agents,
                             sub_1,
                             sub_2,
                             completed_strat) & states
    else:
        raise Exception("eval_strat: unrecognized formula type:" +
                        str(formula))
    lose = states - all_equiv_sat(mas, agents, notlose)
    
    # universal filtering
    if type(formula) is CEX:
        sub_states = post_through(mas,
                                  agents,
                                  Eequiv(mas, agents, states),
                                  completed_strat)
        sub = evalATLK(mas,
                       formula.child,
                       states=sub_states,
                       pre_filtering=pre_filtering)
        win = filter_ax(mas, agents, sub, completed_strat) & states
    elif type(formula) is CEU:
        sub_1 = evalATLK(mas,
                         formula.left,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas,
                         formula.right,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        win = filter_au(mas,
                        agents,
                        sub_1,
                        sub_2,
                        completed_strat) & states
    elif type(formula) is CEW:
        sub_1 = evalATLK(mas,
                         formula.left,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas,
                         formula.right,
                         completed_strat.forsome(mas.bddEnc.inputsCube),
                         pre_filtering=pre_filtering)
        win = filter_aw(mas,
                        agents,
                        sub_1,
                        sub_2,
                        completed_strat) & states
    else:
        raise Exception("eval_strat: unrecognized formula type:" +
                        str(formula))
    win = all_equiv_sat(mas, agents, win)
    
    if (states - (lose | win)).is_false():
        return win
    else:
        new_states = (post_through(mas, agents, BDD.true(mas), strat) -
                      strat.forsome(mas.bddEnc.inputsCube))
        new_moves = new_states & filtered
        compatible = compatible_moves(mas, agents, new_moves, strat)
        if compatible.is_false():
            #return win
            return states - lose
        else:
            states = states - (lose | win)
            for sub_strat in split(mas, agents, compatible):
                win |= eval_alt(mas,
                                formula,
                                agents,
                                states,
                                strat | sub_strat,
                                filtered,
                                pre_filtering=pre_filtering)
                states -= win
                if states.is_false():
                    break
            return win


# ----- universal filtering ---------------------------------------------------

def pre_univ(mas, agents, states, moves):
    """
    Return the set of states q of mas such that for all moves in moves
    specifying an action for agents in q, all successors are in states.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states -- a subset of states of mas;
    moves -- a set of moves for agents.
    """
    agents_cube = mas.inputs_cube_for_agents(agents)
    others_cube = mas.bddEnc.inputsCube - agents_cube
    
    # Abstract away actions of states
    states = states.forsome(mas.bddEnc.inputsCube)
    
    # Abstract away other actions in moves
    moves = moves.forsome(others_cube)
    
    states = states & mas.bddEnc.statesMask
    nstates = ~states & mas.bddEnc.statesMask
    moves = moves & mas.bddEnc.statesInputsMask
    
    res = ~((mas.weak_pre(nstates) & moves).forsome(mas.bddEnc.inputsCube) &
            mas.bddEnc.statesMask) & moves.forsome(mas.bddEnc.inputsCube)
    return res


def stay_univ(mas, agents, states_1, states_2, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states_1 -- a subset of states of mas;
    states_2 -- a subset of states of mas;
    moves -- a set of moves for agents.
    """
    # Abstract away actions of states
    states_1 = states_1.forsome(mas.bddEnc.inputsCube)
    states_2 = states_2.forsome(mas.bddEnc.inputsCube)
    
    states_1 = states_1 & mas.bddEnc.statesMask
    states_2 = states_2 & mas.bddEnc.statesMask
    
    return fixpoint(lambda Z: states_2 |
                              (states_1 & pre_univ(mas, agents, Z, moves)),
                    BDD.true(mas))


def nfair_univ(mas, agents, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    moves -- a closed set of moves for agents.
    """
    # If there are no fairness constraints, there are no nfair states.
    if not mas.fairness_constraints:
        return BDD.false(mas)
    
    else:
        def inner(Z):
            res = BDD.false(mas)
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc & mas.bddEnc.statesMask
                states = stay_univ(mas, agents, Z | nfc, BDD.false(mas), moves)
                res |= pre_univ(mas, agents, states, moves)
            return res
        return fixpoint(inner, BDD.false(mas))


def filter_ax(mas, agents, states, moves):
    """
    Return the set of states of mas for which all fair paths in moves have
    their second state in states.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states -- a subset of states of mas;
    moves -- a closed set of moves for agents.
    """
    return pre_univ(mas,
                    agents,
                    states | nfair_univ(mas, agents, moves),
                    moves)


def filter_au(mas, agents, states_1, states_2, moves):
    """
    Return the set of states of mas for which all fair paths in moves
    reach a state of states_2 through states of states_1.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states_1 -- a subset of states of mas;
    states_2 -- a subset of states of mas;
    moves -- a closed set of moves for agents.
    """
    # Abstract away actions of states
    states_1 = states_1.forsome(mas.bddEnc.inputsCube)
    states_2 = states_2.forsome(mas.bddEnc.inputsCube)
    
    states_1 = states_1 & mas.bddEnc.statesMask
    states_2 = states_2 & mas.bddEnc.statesMask
    
    # If there are no fairness constraints, the computation is simpler
    if not mas.fairness_constraints:
        # mu Q'. states_2 | (states_1 & pre_univ(Q'))
        return fixpoint(lambda Z: states_2 |
                                  (states_1 & pre_univ(mas, agents, Z, moves)),
                        BDD.false(mas))
    
    else:
        states_1_2_n = states_1 | states_2 | nfair_univ(mas, agents, moves)
        def inner(Z):
            res = states_2
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc & mas.bddEnc.statesMask
                states = stay_univ(mas,
                                   agents,
                                   states_1_2_n & (Z | nfc),
                                   states_2 & (Z | nfc),
                                   moves)
                res |= pre_univ(mas, agents, states, moves)
            return res & states_1_2_n
        return fixpoint(inner, BDD.false(mas))


def filter_aw(mas, agents, states_1, states_2, moves):
    """
    Return the set of states of mas for which all fair paths in moves
    reach a state of states_2 through states of states_1, or stay in
    states_1 forever.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states_1 -- a subset of states of mas;
    states_2 -- a subset of states of mas;
    moves -- a closed set of moves for agents.
    """
    # Abstract away actions of states
    states_1 = states_1.forsome(mas.bddEnc.inputsCube)
    states_2 = states_2.forsome(mas.bddEnc.inputsCube)
    
    states_1 = states_1 & mas.bddEnc.statesMask
    states_2 = states_2 & mas.bddEnc.statesMask
    
    # If there are no fairness constraints, the computation is simpler
    if not mas.fairness_constraints:
        # nu Q'. states_2 | (states_1 & pre_univ(Q'))
        return fixpoint(lambda Z: states_2 |
                                  (states_1 & pre_univ(mas, agents, Z, moves)),
                        BDD.true(mas))
    
    else:
        states_1_2_n = states_1 | states_2 | nfair_univ(mas, agents, moves)
        return stay_univ(mas, agents, states_1_2_n, states_2, moves)


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
