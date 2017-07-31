"""
The backward approach.
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
from .common import pre_ce_moves, is_conflicting, split_conflicting
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
    
    pre_filtering has no meaning here, but the argument is kept for
    compatibility.
    
    formula should not be a CAU, CAF, CEW, CEG. If it is the case, a
    NotImplementedError is raised.
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
        raise NotImplementedError("Unsupported formula: " + str(formula))
        
    elif type(formula) is CAF:
        raise NotImplementedError("Unsupported formula: " + str(formula))
        
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
        raise NotImplementedError("Unsupported formula: " + str(formula))
        
    elif type(formula) is CEF:
        # <g> F p = <g> true U p
        new_formula = CEU(formula.group, TrueExp(), formula.child)
        return evalATLK(mas,
                        new_formula,
                        states=states,
                        pre_filtering=pre_filtering)
        
    elif type(formula) is CEW:
        raise NotImplementedError("Unsupported formula: " + str(formula))
                   
    elif type(formula) in {CEX, CEU}:
        return eval_strat(mas,
                          formula,
                          states)
        
    else:
        raise Exception("evalATLK: unrecognized formula type:" + str(formula))


nb_strats = 0

def eval_strat(mas, formula, states):
    """
    Return the BDD representing the subset of the given states of mas
    satisfying formula.
    
    mas -- a multi-agents system;
    formula -- an AST-based ATLK strategic formula;
    states -- a subset of states of mas.
    
    formula must be of type CEX or CEU.
    """
    assert(type(formula) in {CEX, CEU})
    
    agents = [atom.value for atom in formula.group]
    agents = agents_in_list(mas, agents)
    
    global nb_strats
    nb_strats = 0
    
    # Get states equivalent to given states
    equiv_states = Eequiv(mas, agents, states)
    
    if type(formula) is CEX:
        sub = evalATLK(mas,
                        formula.child,
                        states=post_through(mas,
                                            agents,
                                            equiv_states,
                                            BDD.true(mas)))
        sat = BDD.false(mas)
        for strat in split(mas,
                           agents,
                           pre_ce_moves(mas,
                                        agents,
                                        sub & mas.protocol(agents),
                                        BDD.true(mas))):
            win = all_equiv_sat(mas,
                                agents,
                                strat.forsome(mas.bddEnc.inputsCube))
            sat |= win & equiv_states
            equiv_states -= sat
            if equiv_states.is_false():
                break
        return sat & states
    
    elif type(formula) is CEU:
        sub_1 = evalATLK(mas,
                          formula.left,
                          states=reach(mas, equiv_states))
        sub_2 = evalATLK(mas,
                          formula.right,
                          states=reach(mas, equiv_states))
        # unsat are the states such that there exists an equivalent state
        # in equiv_states that is not in sub_1 | sub_2
        unsat = (equiv_states -
                 all_equiv_sat(mas, agents, (sub_1 | sub_2) & equiv_states))
        equiv_states -= unsat
        if equiv_states.is_false():
            return equiv_states
        sat = all_equiv_sat(mas, agents, sub_2 & equiv_states) & equiv_states
        if equiv_states == sat:
            return sat
        equiv_states -= sat
        for strat in split(mas, agents, sub_2 & mas.protocol(agents)):
            sat |= eval_backward_ceu(mas,
                                     agents,
                                     strat,
                                     equiv_states,
                                     sub_1,
                                     sub_2,
                                     BDD.false(mas))
            equiv_states -= sat
            if equiv_states.is_false():
                break
        return sat & states
    
    else:
        raise Exception("eval_strat: unrecognized formula type: " +
                        str(formula))


def eval_backward_ceu(mas, agents, strat, states, sub_1, sub_2, exclude):
    """
    Return the subset of states such that there exists a backward extension of
    strat with states of sub_1 | sub_2.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    strat -- a non-conflicting set of moves of agents;
    states -- a subset of states of mas such that states = [states]^E_agents;
    sub_1 -- a subset of states of mas;
    sub_2 -- a subset of states of mas.
    
    The states of strat must be in sub_1 | sub_2.
    """
    global nb_strats
    nb_strats += 1
    if nb_strats % GC_FREQUENCE == 0:
        gc.collect()
    
    strat_states = strat.forsome(mas.bddEnc.inputsCube)
    
    notlose = filter_ceu(mas,
                         agents,
                         sub_1,
                         strat_states,
                         mas.protocol(agents))
    lose = states - (all_equiv_sat(mas, agents, notlose) & states)
    states -= lose
    if states.is_false():
        return states
    
    win = all_equiv_sat(mas, agents, strat_states) & states
    states -= win
    if states.is_false():
        return win
    
    sat = win
    
    new_moves = ((pre_ce_moves(mas,
                               agents,
                               strat,
                               mas.protocol(agents) - exclude) &
                  sub_1) - strat) & mas.bddEnc.statesInputsMask
    compatible = compatible_moves(mas, agents, new_moves, strat)
    if compatible.is_false():
        return sat
    
    states -= sat
    
    for new_strat in split_all(mas, agents, compatible):
        sat |= eval_backward_ceu(mas,
                                 agents,
                                 strat | new_strat,
                                 states,
                                 sub_1,
                                 sub_2,
                                 exclude | (new_moves - new_strat))
        states -= sat
        if states.is_false():
            return sat
    return sat


# ---- split ------------------------------------------------------------------

def split_one_all(mas, agents, agent, moves):
    """
    Split one equivalence class of moves and return couples composed of
    a split and the rest of moves to split; the last couple is the rest of
    moves to split only, the split being empty.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    moves -- a subset of moves for agents.
    
    Return a generator of all couples of splits and rest of moves, the last
    couple containing an empty split.
    
    """
    if moves.is_false():
        yield (moves, moves)
        return
        
    else:
        # Get one equivalence class
        si = mas.pick_one_state_inputs(moves)
        s = si.forsome(mas.bddEnc.inputsCube)
        eqs = get_equiv_class(mas, [agent], s)
        eqcl = moves & eqs
        
        # Remove it from strats
        moves = moves - eqcl
        
        # The current equivalence class is conflicting
        for non_conflicting in split_conflicting(mas,
                                                 agents,
                                                 agent,
                                                 eqcl):
            yield (non_conflicting, moves)
        yield (BDD.false(mas.bddEnc.DDmanager), moves)
        return


def split_agent_all(mas, agents, agent, moves):
    """
    Split the given set of moves for agents into its greatest subsets
    non-conflicting for agent.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    moves -- a subset of moves for agents.
    """
    if moves.is_false():
        yield moves
    else:
        for nc, rest in split_one_all(mas, agents, agent, moves):
            for strat in split_agent_all(mas, agents, agent, rest):
                yield nc | strat


def split_all(mas, agents, moves):
    """
    Split the given moves for agents into all its non-conflicting greatest
    subsets.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas (as a list);
    moves -- a subset of moves for agents.
    
    Return a generator of all non-conflicting greatest subsets of moves.
    """
    if not agents:
        yield moves
    else:
        agent = agents[0]
        others = agents[1:]
        seen = {BDD.false(mas)}
        for others_strat in split_all(mas, others, moves):
            for strat in split_agent_all(mas, agents, agent, others_strat):
                if strat not in seen:
                    seen.add(strat)
                    yield strat
