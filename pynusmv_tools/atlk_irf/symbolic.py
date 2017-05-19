"""
The naive approach, with and without pre-filtering.
"""

import operator
from functools import reduce
from collections import OrderedDict

from pynusmv.dd import BDD
from pynusmv.fsm import BddTrans
from pynusmv.mc import eval_simple_expression
from pynusmv.utils import fixpoint
from pynusmv import model
from pynusmv import glob
from pynusmv import node

from ..atlkFO.ast import (TrueExp, FalseExp, Init, Reachable,
                          Atom, Not, And, Or, Implies, Iff, 
                          AF, AG, AX, AU, AW, EF, EG, EX, EU, EW,
                          nK, nE, nD, nC, K, E, D, C,
                          CEF, CEG, CEX, CEU, CEW, CAF, CAG, CAX, CAU, CAW)
from ..atlkFO.eval import (fair_states, nk, ne, nd, nc)

from .common import *
from .utils import *

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
        # EG p = E p W false
        new_formula = EW(formula.child, FalseExp())
        return evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is AG:
        # AG p = ~EF ~p = ~E[ true U ~p ]
        new_formula = EF(Not(formula.child))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is EU:
        return eu(mas,
                  evalATLK(mas, formula.left, pre_filtering=pre_filtering),
                  evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
    elif type(formula) is AU:
        # A[p U q] = ~E[~q W ~p & ~q] = ~(E[~q U ~p & ~q] | EG ~q)
        new_formula = EW(Not(formula.right),
                         And(Not(formula.left), Not(formula.right)))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is EF:
        # EF p = E true U p
        new_formula = EU(TrueExp(), formula.child)
        return evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is AF:
        # AF p = ~EG ~p
        new_formula = EG(Not(formula.child))
        return ~evalATLK(mas, new_formula, pre_filtering=pre_filtering)
        
    elif type(formula) is EW:
        return ew(mas,
                  evalATLK(mas, formula.left, pre_filtering=pre_filtering),
                  evalATLK(mas, formula.right, pre_filtering=pre_filtering))
        
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
    
    # Encode strategies
    encode_strategies(mas, agents, formula, filtered)

    # Compute the set of winning states
    if type(formula) is CEX:
        sub = evalATLK(mas, formula.child, pre_filtering=pre_filtering)
        winning = eval_cex(mas, formula, agents, sub)
    elif type(formula) is CEU:
        sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        winning = eval_ceu(mas, formula, agents, sub_1, sub_2)
    elif type(formula) is CEW:
        sub_1 = evalATLK(mas, formula.left, pre_filtering=pre_filtering)
        sub_2 = evalATLK(mas, formula.right, pre_filtering=pre_filtering)
        winning = eval_cew(mas, formula, agents, sub_1, sub_2)
    else:
        raise Exception("eval_strat: unrecognized formula type:" +
                        str(formula))
    
    winning = (winning.forsome(mas.bddEnc.inputsCube) & mas.reachable_states)
    return winning


# ----- Encoding strategies ---------------------------------------------------

def encode_strategies(mas, agents, formula, filtered):
    """
    Encode the strategies for agents, to check formula, given the filtered
    moves.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    formula -- an ATLK_irF strategic formula where the group is agents;
    filtered -- either the complete protocol of the agents, or the filtered
                moves for agents, for the given formula.
    
    The result is the presence, in mas.transitions[formula], of three relations
    under the "jump", "equiv", and "follow" keys, to perform the model
    checking:
        * the "jump" relation encode the fact that the original state stays the
          same and all strategies can change;
        * the "equiv" relation encode the fact that the states are equivalent
          for some agent in the group of formula, and the strategies of these
          agents are kept the same;
        * the "follow" relation encode the original transition relation with
          each agent of the group of formula following his strategy encoded
          in the current state (and that these strategies are kept the same).
    
    Note: mas.encoded is populated with intermediate cached information:
        * mas.encoded[(agent, filtered)] gives two (model-based) relations:
          + the relation encoding the fact that the encoded strategies of agent
            from filtered are kept the same;
          + the relation encoding the fact that the encoded strategies of agent
            are followed;
          they only depends on the agent and the filtered moves, thus if two
          sub-formulas have the same filtered moves (e.g., pre-filtering is
          not used), the relations are the same;
        * mas.encoded[agent] gives the relation encoding the equivalence for
          agent;
          it only depends on agent, since it only depends on what he observes;
          THIS RELATION DOES NOT ENCODE THE FACT THAT THE STRATEGIES DO NOT
          CHANGE;
        * mas.encoded["jump"] gives the relation encoding the fact that the
          state is the same but the strategies can change;
          it only depends on the MAS, since all strategies are free and only
          the state is kept identical.
    """
    if not hasattr(mas, "transitions"):
        mas.transitions = {}
    if not hasattr(mas, "encoded"):
        mas.encoded = {}
    
    
    # if mas.encoded["jump"] does not exist,
    # encode it, based on the original state variables of the model
    if "jump" not in mas.encoded:
        jump = jump_relation(mas)
        mas.encoded["jump"] = jump
    
    
    # Encode each agent variables and relations if needed
    
    # for each agent in agents,
    # if (agent, filtered) is not in mas.encoded,
    # compute them
    for agent in agents:
        if (agent, filtered) not in mas.encoded:
            relations = strategy_relations(mas, agents, agent, filtered)
            mas.encoded[(agent, filtered)] = relations
    
    # for each agent in agents,
    # if mas.encoded[agent] is not present,
    # compute it
    for agent in agents:
        if agent not in mas.encoded:
            relation = equivalence_relation(mas, agent)
            mas.encoded[agent] = relation
    
    
    # Encode the transition relations
    if formula not in mas.transitions:
        mas.transitions[formula] = {}
    
    # the "jump" relation is just mas.encoded["jump"]
    if "jump" not in mas.transitions[formula]:
        jump = mas.encoded["jump"]
        trans = BddTrans.from_string(mas.bddEnc.symbTable, str(jump))
        mas.transitions[formula]["jump"] = trans
    
    # the "equiv" relation is based on
    # * the "equiv" relations of each agent in agents
    #   (disjunction, for group knowledge)
    # * the strategies of the agents are the same
    #   (based on the variables of each agent, stored in
    #    mas.encoded[(agent, filtered)])
    if "equiv" not in mas.transitions[formula]:
        equiv = reduce(operator.or_,
                       (mas.encoded[agent] for agent in agents),
                       model.Falseexp())
        equiv = reduce(operator.and_,
                       (mas.encoded[(agent, filtered)][0] for agent in agents),
                       equiv)
        trans = BddTrans.from_string(mas.bddEnc.symbTable, str(equiv))
        mas.transitions[formula]["equiv"] = trans
    
    # the "follow" relation is based on
    # * the original transition relation of the MAS;
    # * the fact that the strategies of the agents are the same,
    #   and that the strategies for agents are followed by these agents,
    #   given by the variables in mas.encoded[(agent, filtered)]
    if "follow" not in mas.transitions[formula]:
        flat = glob.flat_hierarchy()
        follow = reduce(operator.and_,
                        (mas.encoded[(agent, filtered)][0] &
                         mas.encoded[(agent, filtered)][1]
                         for agent in agents),
                        flat.trans)
        trans = BddTrans.from_string(mas.bddEnc.symbTable, str(follow))
        mas.transitions[formula]["follow"] = trans


def jump_relation(mas):
    """
    Return the transition relation corresponding to the "jump" relation of the
    given MAS.
    
    mas -- a multi-agents system.
    
    The returned value is a model-based relation encoding the fact that all
    original state variables of the given MAS stay the same, and other encoded
    variables are free to change.
    """
    # Get the original state variables
    flat = glob.flat_hierarchy()
    symb_table = mas.bddEnc.symbTable
    original_variables = [variable for variable in flat.variables
                          if symb_table.is_state_var(variable)]
    
    # Build the relation expression
    return reduce(operator.and_,
                  (variable.next() == variable
                   for variable in original_variables))


def strategy_relations(mas, agents, agent, filtered):
    """
    Extract and encode the variables representing the strategies of agent in
    filtered, and return
    * the relation encoding the fact that the encoded strategies of agent
      from filtered are kept the same;
    * the relation encoding the fact that the encoded strategies of agent
      are followed;
    
    mas -- a multi-agents system;
    agents -- a set of agents of mas;
    agent -- an agent from agents;
    filtered -- a set of agents-moves.
    
    The returned value is a couple where the first element is the first
    relation, and the second element is the second relation.
    
    The new variables are encoded on a new layer called agent_hash(filtered).
    """
    # Get observable variables and actions for agent
    observables = mas.agents_observed_variables[agent]
    actions = mas.agents_inputvars[agent]
    
    act_cube = mas.bddEnc.cube_for_inputs_vars(actions)
    obs_cube = mas.bddEnc.cube_for_state_vars(observables)
    state_cube = mas.bddEnc.statesCube
    inputs_cube = mas.bddEnc.inputsCube
    other_vars_cube = state_cube - obs_cube
    other_acts_cube = inputs_cube - act_cube
    
    
    new_layer = str(agent) + "_" + str(hash(filtered))
    
    
    # Extract the useful information from filtered
    variables = OrderedDict()
    protocol = (filtered &
                mas.state_constraints &
                mas.inputs_constraints &
                mas.bddEnc.statesInputsMask)
    while protocol.isnot_false():
        si = mas.pick_one_state_inputs(protocol)
        state = mas.pick_one_state(si.forsome(mas.bddEnc.inputsCube))
        
        # Get observation values
        obs_vars = tuple(sorted([(node.Identifier.from_string(var),
                                  node.Expression.from_string(val))
                                 for var, val
                                 in state.get_str_values().items()
                                 if var in observables]))
        
        variables[obs_vars] = list()
        inputs = ((protocol &
                   state.forsome(other_vars_cube)).forsome(
                   mas.bddEnc.statesCube)
                  & mas.bddEnc.statesInputsMask
                  & mas.bddEnc.statesMask
                  & mas.bddEnc.inputsMask
                  & mas.state_constraints
                  & mas.inputs_constraints)
        # Get the possible values for actions
        while inputs.isnot_false():
            i = mas.pick_one_inputs(inputs)
            
            inputs_vars = tuple(sorted(
                          [(node.Identifier.from_string(var),
                            node.Expression.from_string(val))
                           for var, val in i.get_str_values().items()
                           if var in actions]))
            variables[obs_vars].append(inputs_vars)
            
            inputs = inputs - i.forsome(other_acts_cube)
        
        protocol = (protocol - state.forsome(other_vars_cube))
    
    
    # Compute the variables for the strategies of agent in filtered
    new_variables = []
    strategies = list()  # strategies is a list of tuples
                         #   (obs assigment,
                         #    corresponding strategy var,
                         #    corresponding strategy var value,
                         #    actions assigment)
    for obs_values in variables:
        var_name = (new_layer + "_" + assign_to_name(obs_values))
        var_name = node.Identifier.from_string(var_name)
        type_values = []
        for action_values in variables[obs_values]:
            type_value = assign_to_name(action_values)
            type_values.append(type_value)
            
            strategies.append((obs_values,
                               var_name,
                               type_value,
                               action_values))
        
        var_type = mas.bddEnc.symbTable._get_type_from_node(node.Scalar(
                                                                  type_values))
        
        # a triplet (variable name (as Nodes),
        #            variable type (as SymbType),
        #            variable kind (as int))
        new_variables.append((var_name,
                              var_type,
                              mas.bddEnc.symbTable.SYMBOL_STATE_VAR))
    
    new_variables = sorted(new_variables, key=lambda e: str(e[0]))
    strategies = sorted(strategies, key=lambda e: str(e[1]))
    
    
    # Encode them
    symb_table = mas.bddEnc.symbTable
    symb_table.create_layer(new_layer)
    
    # Encode variables
    for var, type_, kind in new_variables:
        if kind is symb_table.SYMBOL_STATE_VAR:
            symb_table.declare_state_var(new_layer, var, type_)
        elif kind is symb_table.SYMBOL_FROZEN_VAR:
            symb_table.declare_frozen_var(new_layer, var, type_)
        elif kind is symb_table.SYMBOL_INPUT_VAR:
            symb_table.declare_input_var(new_layer, var, type_)
    glob.encode_variables_for_layers(layers=[new_layer])
    
    
    # Build the relation
    # strategy stays the same
    strategy_stay = reduce(operator.and_,
                           (var.next() == var for var, _, _ in new_variables))
    
    # actions are followed:
    #   observations are true
    #   & corresponding strategy var is ivar#value##...
    #   ->
    #   ivar = value & ...
    # strategies is a set of tuples
    #   (obs assigment,
    #    corresponding strategy var,
    #    corresponding strategy var value,
    #    actions assigment)
    trans = []
    for move in strategies:
        obs_assign, strat_var, strat_val, act_assign = move
        
        trans_cond = reduce(lambda e, n: e & n,
                            [var == val for var, val in obs_assign],
                            node.Trueexp())
        trans_cond = trans_cond & (strat_var == strat_val)
        
        trans_cons = reduce(lambda e, n: e & n,
                            [var == val for var, val in act_assign],
                            node.Trueexp())
        trans.append(trans_cond.implies(trans_cons))
    followed = reduce(operator.and_, trans)
    
    return strategy_stay, followed


def equivalence_relation(mas, agent):
    """
    Return the (text-based) transition relation corresponding to the
    observations of agent in mas.
    
    mas -- a multi-agents system;
    agent -- an agent of mas.
    
    The returned value is the model-encoded transition relation telling that
    agent's observations are kept the same.
    """
    # compute the relation based on the observable variables of the agent
    trans = reduce(operator.and_,
                   [node.Identifier.from_string(str(obs)) ==
                    node.Identifier.from_string(str(obs)).next()
                    for obs in mas.agents_observed_variables[agent]],
                   node.Trueexp())
    return trans


# ----- eval algorithms -------------------------------------------------------

def _nfair(mas, formula, agents):
    """
    Return the set of states in which the given agents cannot avoid a fair path
    by using the strategy encoded in these states.
    """
    jump = mas.transitions[formula]["jump"]
    equiv = mas.transitions[formula]["equiv"]
    follow = mas.transitions[formula]["follow"]
    
    if not mas.fairness_constraints:
        return BDD.false(mas)
    
    else:
        # nfair =
        # mu Z. \/_fc []_group_follow(nu Y. (Z \/ ~fc) /\ []_group_follow(Y))
        def inner(Z):
            # \/_fc []_group_follow(nu Y. (Z \/ ~fc) /\ []_group_follow(Y))
            res = BDD.false(mas)
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc
                res = res | ~follow.pre(~fixpoint(lambda Y: (Z | nfc) &
                                                            ~follow.pre(~Y),
                                                  BDD.true(mas)))
            return res
        res = fixpoint(inner, BDD.false(mas))
        return res


def eval_cex(mas, formula, agents, states):
    jump = mas.transitions[formula]["jump"]
    equiv = mas.transitions[formula]["equiv"]
    follow = mas.transitions[formula]["follow"]
    reachable = mas.reachable_states
    
    if not mas.fairness_constraints:
        # <group>i X p =
        # <>_group_jump []_group_equiv (reachable => []_group_follow p)
        return jump.pre(~equiv.pre(~(reachable.imply(~follow.pre(~states)))))
    else:
        # <group>i X fair p =
        # <>_group_jump []_group_equiv
        # (reachable => []_group_follow (p \/ ~ifair))
        return jump.pre(~equiv.pre(~(reachable.imply(
                        ~follow.pre(~(states |
                                      _nfair(mas, formula, agents)))))))


def eval_ceu(mas, formula, agents, states_1, states_2):
    jump = mas.transitions[formula]["jump"]
    equiv = mas.transitions[formula]["equiv"]
    follow = mas.transitions[formula]["follow"]
    reachable = mas.reachable_states
    
    if not mas.fairness_constraints:
        # <group>i[p U q] =
        # <>_group_jump []_group_equiv
        # (reachable => mu Z . q \/ (p /\ []_group_follow Z))
        return jump.pre(~equiv.pre(~(reachable.imply(
                        fixpoint(lambda Z: states_2 |
                                           (states_1 & ~follow.pre(~Z)),
                                 BDD.false(mas))))))
    else:
        nfair = _nfair(mas, formula, agents)
        # <group>i fair [p U q] =
        # <>_group_jump []_group_equiv
        # reachable =>
        # mu Z. (p \/ q \/ ~ifair) /\
        #       (q \/_fc []_group_follow
        #                (nu Y. (Z \/ ~fc) /\
        #                              (p \/ q \/ ~ifair) /\
        #                              (q \/ []_group_follow(Y))))
        def inner(Z):
            # (p \/ q \/ ~ifair) /\
            # (q \/_fc []_group_follow
            #          (nu Y. (Z \/ ~fc) /\
            #                        (p \/ q \/ ~ifair) /\
            #                        (q \/ []_group_follow(Y))))
            res = BDD.false(mas)
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc
                # []_group_follow (nu Y. (Z \/ ~fc) /\
                #                        (p \/ q \/ ~ifair) /\
                #                        (q \/ []_group_follow(Y)))
                res = res | ~follow.pre(
                      ~(fixpoint(lambda Y: ((Z | nfc) &
                                            (states_1 | states_2 | nfair) &
                                            (states_2 | ~follow.pre(~Y))),
                                 BDD.true(mas))))
            return ((states_1 | states_2 | nfair) & (states_2 | res))
        return jump.pre(~equiv.pre(~(reachable.imply(
                        fixpoint(inner, BDD.false(mas))))))


def eval_cew(mas, formula, agents, states_1, states_2):
    jump = mas.transitions[formula]["jump"]
    equiv = mas.transitions[formula]["equiv"]
    follow = mas.transitions[formula]["follow"]
    reachable = mas.reachable_states
    
    if not mas.fairness_constraints:
        # <group>i[p W q] = 
        # <>_group_jump []_group_equiv
        # (reachable => nu Z . q \/ (p /\ []_group_follow Z))
        return jump.pre(~equiv.pre(~(reachable.imply(
                        fixpoint(lambda Z: states_2 |
                                           (states_1 & ~follow.pre(~Z)),
                                 BDD.true(mas))))))
    else:
        nfair = _nfair(mas, formula, agents)
        # <group>i fair [p W q] =
        # <>_group_jump []_group_equiv
        # reachable =>
        # nu Z. (p \/ q \/ ~ifair) /\ (q \/ []_group_follow(Z))
        res = jump.pre(~equiv.pre(~(reachable.imply(
                       fixpoint(lambda Z: ((states_1 | states_2 | nfair) &
                                           (states_2 | ~follow.pre(~Z))),
                                BDD.true(mas))))))
        return res


# ----- CTL algorithms --------------------------------------------------------

def _fair(mas):
    if not mas.fairness_constraints:
        return BDD.true(mas)
    else:
        run = mas.trans
        # fair = nu Z. /\_fc pre(mu Y. (Z /\ fc) \/ pre(Y))
        def inner(Z):
            res = BDD.true(mas)
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                res = res & run.pre(fixpoint(lambda Y: (Z & fc) | run.pre(Y),
                                             BDD.false(mas)))
            return res
        return fixpoint(inner, BDD.true(mas))


def ex(mas, states):
    run = mas.trans
    return run.pre(states & _fair(mas))

def eu(mas, states_1, states_2):
    run = mas.trans
    return fixpoint(lambda Y : (states_2 & _fair(mas)) |
                               (states_1 & run.pre(Y)),
                    BDD.false(mas))


def ew(mas, states_1, states_2):
    run = mas.trans
    if not mas.fairness_constraints:
        return fixpoint(lambda Z: states_2 | (states_1 & run.pre(Z)),
                        BDD.true(mas))
    else:
        def inner(Z):
            res = BDD.true(mas)
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                res = res & run.pre(fixpoint(lambda Y: (states_2 & _fair(mas))
                                                       |
                                                       (Z & fc) |
                                                       (states_1 & run.pre(Y)),
                                             BDD.false(mas)))
            return (res & states_1) | (states_2 & _fair(mas))
        return fixpoint(inner, BDD.true(mas))


# ----- caching ---------------------------------------------------------------

__evalATLK_cache = {}
__orig_evalATLK = evalATLK
def __cached_evalATLK(mas, formula, pre_filtering=False):
    if (mas, formula) not in __evalATLK_cache:
        sat = __orig_evalATLK(mas, formula, pre_filtering=pre_filtering)
        __evalATLK_cache[(mas, formula)] = sat
    return __evalATLK_cache[(mas, formula)]
evalATLK = __cached_evalATLK
