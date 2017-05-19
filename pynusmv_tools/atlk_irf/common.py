"""
The common functions needed by the approaches.

* The filter and filter^M algorithms;
* The split and split_agent algorithms.
"""

from pynusmv.dd import BDD
from pynusmv.utils import fixpoint


__all__ = ["filter_cex", "filter_ceu", "filter_cew",
           "filter_cex_moves", "filter_ceu_moves", "filter_cew_moves",
           "split", "get_equiv_class",
           "all_equiv_sat", "post_through", "compatible_moves"]


# ----- filter algorithms -----------------------------------------------------

def pre_ce(mas, agents, states, moves):
    """
    Return the set of states of mas such that there exists a move for agents
    in moves such that all reached states are in states.
    
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
    
    return (
            (
             ~(mas.weak_pre(nstates).forsome(others_cube))
             &
             mas.weak_pre(states)
            ).forsome(others_cube)
            &
            moves
           ).forsome(mas.bddEnc.inputsCube)


def stay_ce(mas, agents, states_1, states_2, moves):
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
                              (states_1 & pre_ce(mas, agents, Z, moves)),
                    BDD.true(mas))


def nfair_ce(mas, agents, moves):
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
                states = stay_ce(mas, agents, Z | nfc, BDD.false(mas), moves)
                res |= pre_ce(mas, agents, states, moves)
            return res
        return fixpoint(inner, BDD.false(mas))


def filter_cex(mas, agents, states, moves):
    """
    Return the set of states of mas for which there exists a strategy for
    agents compatible with moves such that all fair paths enforced by the
    strategy have their second state in states.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    states -- a subset of states of mas;
    moves -- a closed set of moves for agents.
    """
    return pre_ce(mas, agents, states | nfair_ce(mas, agents, moves), moves)


def filter_ceu(mas, agents, states_1, states_2, moves):
    """
    Return the set of states of mas for which there exists a strategy for
    agents compatible with moves such that all fair paths enforced by the
    strategy reach a state of states_2 through states of states_1.
    
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
        # mu Q'. states_2 | (states_1 & pre_ce(Q'))
        return fixpoint(lambda Z: states_2 |
                                  (states_1 & pre_ce(mas, agents, Z, moves)),
                        BDD.false(mas))
    
    else:
        states_1_2_n = states_1 | states_2 | nfair_ce(mas, agents, moves)
        def inner(Z):
            res = states_2
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc & mas.bddEnc.statesMask
                states = stay_ce(mas,
                                 agents,
                                 states_1_2_n & (Z | nfc),
                                 states_2 & (Z | nfc),
                                 moves)
                res |= pre_ce(mas, agents, states, moves)
            return res & states_1_2_n
        return fixpoint(inner, BDD.false(mas))


def filter_cew(mas, agents, states_1, states_2, moves):
    """
    Return the set of states of mas for which there exists a strategy for
    agents compatible with moves such that all fair paths enforced by the
    strategy reach a state of states_2 through states of states_1, or stay in
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
        # nu Q'. states_2 | (states_1 & pre_ce(Q'))
        return fixpoint(lambda Z: states_2 |
                                  (states_1 & pre_ce(mas, agents, Z, moves)),
                        BDD.true(mas))
    
    else:
        states_1_2_n = states_1 | states_2 | nfair_ce(mas, agents, moves)
        return stay_ce(mas, agents, states_1_2_n, states_2, moves)


# ----- filter^M algorithms ---------------------------------------------------

def pre_ce_moves(mas, agents, target, moves):
    """
    Return the set of moves of mas such that there exists a move for agents
    in moves such that all reached states have a move in target.
    
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    target -- a subset of moves for agents;
    moves -- a set of moves for agents.
    """ 
    agents_cube = mas.inputs_cube_for_agents(agents)
    others_cube = mas.bddEnc.inputsCube - agents_cube
    
    # Abstract away actions of states
    states = target.forsome(mas.bddEnc.inputsCube)
    
    # Abstract away other actions in moves
    moves = moves.forsome(others_cube)
    
    states = states & mas.bddEnc.statesMask
    nstates = ~states & mas.bddEnc.statesMask
    moves = moves & mas.bddEnc.statesInputsMask
    
    return (
            (
             ~(mas.weak_pre(nstates).forsome(others_cube))
             &
             mas.weak_pre(states)
            ).forsome(others_cube)
            &
            moves
           ).forsome(others_cube)


def stay_ce_moves(mas, agents, moves_1, moves_2, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    moves_1 -- a subset of moves for agents;
    moves_2 -- a subset of moves for agents;
    moves -- a set of moves for agents.
    """
    agents_cube = mas.inputs_cube_for_agents(agents)
    others_cube = mas.bddEnc.inputsCube - agents_cube
    
    # Abstract away actions of states
    moves_1 = moves_1.forsome(others_cube)
    moves_2 = moves_2.forsome(others_cube)
    
    moves_1 = moves_1 & mas.bddEnc.statesInputsMask
    moves_2 = moves_2 & mas.bddEnc.statesInputsMask
    
    return fixpoint(lambda Z: moves_2 |
                              (moves_1 & pre_ce_moves(mas, agents, Z, moves)),
                    BDD.true(mas))


def nfair_ce_moves(mas, agents, moves):
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
                nfc_moves = nfc & mas.protocol(agents) & moves
                m = stay_ce_moves(mas,
                                  agents,
                                  Z | nfc_moves,
                                  BDD.false(mas),
                                  moves)
                res |= pre_ce_moves(mas, agents, m, moves)
            return res
        return fixpoint(inner, BDD.false(mas))


def filter_cex_moves(mas, agents, target, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    target -- a subset of moves for agents;
    moves -- a closed set of moves for agents.
    """
    return pre_ce_moves(mas,
                        agents,
                        target & mas.protocol(agents) |
                        nfair_ce_moves(mas, agents, moves), moves)


def filter_ceu_moves(mas, agents, moves_1, moves_2, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    moves_1 -- a subset of moves for agents;
    moves_2 -- a subset of moves for agents;
    moves -- a closed set of moves for agents.
    """
    # Abstract away actions of states
    states_1 = moves_1.forsome(mas.bddEnc.inputsCube)
    states_2 = moves_2.forsome(mas.bddEnc.inputsCube)
    
    states_1 = states_1 & mas.bddEnc.statesMask
    states_2 = states_2 & mas.bddEnc.statesMask
    
    moves_1 = states_1 & mas.protocol(agents)
    moves_2 = states_2 & mas.protocol(agents)
    
    # If there are no fairness constraints, the computation is simpler
    if not mas.fairness_constraints:
        # mu Q'. moves_2 & moves | (moves_1 & moves & pre_ce_moves(Q'))
        return fixpoint(lambda Z: moves_2 & moves |
                                  (moves_1 &
                                   moves &
                                   pre_ce_moves(mas, agents, Z, moves)),
                        BDD.false(mas))
    
    else:
        moves_1_2_n = moves_1 | moves_2 | nfair_ce_moves(mas, agents, moves)
        moves_1_2_n = moves_1_2_n & moves
        def inner(Z):
            res = moves_2 & moves
            for fc in mas.fairness_constraints:
                fc = fc.forsome(mas.bddEnc.inputsCube)
                nfc = ~fc & mas.bddEnc.statesMask
                moves_nfc = nfc & mas.protocol(agents) & moves
                m = stay_ce_moves(mas,
                                  agents,
                                  moves_1_2_n & (Z | moves_nfc),
                                  moves_2 & moves & (Z | moves_nfc),
                                  moves)
                res |= pre_ce_moves(mas, agents, m, moves)
            return res & moves_1_2_n
        return fixpoint(inner, BDD.false(mas))


def filter_cew_moves(mas, agents, moves_1, moves_2, moves):
    """
    mas -- a multi-agent system;
    agents -- a subset of agents of mas;
    moves_1 -- a subset of moves for agents;
    moves_2 -- a subset of moves for agents;
    moves -- a closed set of moves for agents.
    """
    # Abstract away actions of states
    states_1 = moves_1.forsome(mas.bddEnc.inputsCube)
    states_2 = moves_2.forsome(mas.bddEnc.inputsCube)
    
    states_1 = states_1 & mas.bddEnc.statesMask
    states_2 = states_2 & mas.bddEnc.statesMask
    
    moves_1 = states_1 & mas.protocol(agents)
    moves_2 = states_2 & mas.protocol(agents)
    
    # If there are no fairness constraints, the computation is simpler
    if not mas.fairness_constraints:
        # nu Q'. moves_2 & moves | (moves_1 & moves & pre_ce(Q'))
        return fixpoint(lambda Z: moves_2 & moves |
                                  (moves_1 & moves &
                                  pre_ce_moves(mas, agents, Z, moves)),
                        BDD.true(mas))
    
    else:
        moves_1_2_n = moves_1 | moves_2 | nfair_ce_moves(mas, agents, moves)
        moves_1_2_n = moves_1_2_n & moves
        return stay_ce_moves(mas, agents, moves_1_2_n, states_2 & moves, moves)


# ----- split algorithms ------------------------------------------------------

def get_equiv_class(mas, agents, states):
    """
    Return the equivalence class for agents states belong to. The group
    knowledge based equivalence class for agents containing some state of
    states is returned.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    states -- a subset states of mas.
    """
    # The group knowledge based equivalence classes of states for agents
    # is the set of states q' for which there exists an agent ag in agents
    # and a state q in states such that q' sim_ag q.
    
    res = states
    for agent in agents:
        res |= (mas.equivalent_states(states, {agent}) & mas.reachable_states)
    return res


def is_conflicting(fsm, agents, agent, eqclass):
    """
    Return whether the given equivalence class for agent is conflicting or not.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    eqclass -- a subset of moves for agents composed of states equivalent for
               agent.
    
    """
    si = fsm.pick_one_state_inputs(eqclass)
    others_cube = fsm.bddEnc.inputsCube - fsm.inputs_cube_for_agents({agent})
    return (eqclass -
            (eqclass &
             si.forsome(fsm.bddEnc.statesCube | others_cube)
            )
           ).isnot_false()


def split_conflicting(mas, agents, agent, eqclass):
    """
    Split the given equivalence class for agent into non conflicting subsets.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    eqclass -- a subset of moves for agents composed of states equivalent for
               agent.
    
    Generate all splitted non conflicting subsets.
    """
    others_cube = mas.bddEnc.inputsCube - mas.inputs_cube_for_agents({agent})
    # Split eqclass into non-conflicting subsets
    while eqclass.isnot_false():
        si = mas.pick_one_state_inputs(eqclass)
        ncss = eqclass & si.forsome(mas.bddEnc.statesCube | others_cube)
        eqclass = eqclass - ncss
        yield ncss


def split_one(mas, agents, agent, moves):
    """
    Split one equivalence class of moves and return triples composed of
    the common non-conflicting part already encountered, a split and the rest
    of moves to split.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    moves -- a subset of moves for agents.
    
    Return a generator of all triples of common parts, splits and rest of
    moves.
    
    """
    if moves.is_false():
        yield (moves, moves, moves)
        return
        
    else:
        common = BDD.false(mas.bddEnc.DDmanager)
        
        while moves.isnot_false():
            # Get one equivalence class
            si = mas.pick_one_state_inputs(moves)
            s = si.forsome(mas.bddEnc.inputsCube)
            eqs = get_equiv_class(mas, [agent], s)
            eqcl = moves & eqs
            
            # Remove it from strats
            moves = moves - eqcl
            
            # The current equivalence class is conflicting
            if is_conflicting(mas, agents, agent, eqcl):
                for non_conflicting in split_conflicting(mas,
                                                         agents,
                                                         agent,
                                                         eqcl):
                    yield (common, non_conflicting, moves)
                return
            
            else:
                # Add equivalence class to common
                common = common | eqcl
        
        # strats is false, everything is in common
        yield (common, moves, moves)
        return


def split_agent(mas, agents, agent, moves):
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
        for common, nc, rest in split_one(mas, agents, agent, moves):
            for strat in split_agent(mas, agents, agent, rest):
                yield common | nc | strat


def split(mas, agents, moves):
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
        for others_strat in split(mas, others, moves):
            for strat in split_agent(mas, agents, agent, others_strat):
                yield strat


# ----- others ----------------------------------------------------------------

def all_equiv_sat(mas, agents, states):
    """
    Return the subset of states such that all states indistinguishable
    from s by agents are in states.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas (as a list);
    states -- a subset of states of mas.
    
    """
    equiv_sat = states
    missing = ~states & mas.bddEnc.statesInputsMask
    for agent in agents:
        equiv_sat &= ~mas.equivalent_states(missing & mas.reachable_states,
                                            {agent}) & states
    return equiv_sat


def post_through(mas, agents, states, moves):
    """
    Return the set of states reachable from the given states through actions of
    agents allowed by the given moves for agents.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    states -- a subset of states of mas;
    moves -- a subset of moves for agents.
    """
    return mas.post(states & moves)


def compatible_moves(mas, agents, moves, filtered):
    """
    Return the subset of given moves for agents that are compatible with the
    filtered set of moves.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    moves -- a subset of moves for agents;
    filtered -- a subset of moves for agents.
    """
    for agent in agents:
        moves = compatible_moves_for_agent(mas, agents, agent, moves, filtered)
    return moves


def compatible_moves_for_agent(mas, agents, agent, moves, filtered):
    """
    Return the subset of given moves for agents that are non-agent-conflicting
    with the filtered set of moves.
    
    mas -- a multi-agents system;
    agents -- a subset of agents of mas;
    agent -- an agent of agents;
    moves -- a subset of moves for agents;
    filtered -- a subset of moves for agents.
    """
    agent_cube = mas.inputs_cube_for_agents({agent})
    others_cube = mas.bddEnc.inputsCube - agent_cube
    
    compatible = BDD.false(mas)
    while moves.isnot_false():
        # Get one equivalence class of states from moves
        si = mas.pick_one_state_inputs(moves)
        s = si.forsome(mas.bddEnc.inputsCube)
        eqs = get_equiv_class(mas, {agent}, s)
        
        # Get the corresponding moves and remove them from moves
        eqcl = moves & eqs
        moves -= eqcl
        
        # If there are no states in filtered for some of these moves,
        # the class can be added to compatible
        if (eqs & filtered).is_false():
            compatible |= eqcl
        
        # Otherwise, the only possible action for agent is the one defined
        # by filtered for this class
        else:
            # So add to compatible the states for which the action for agent
            # is the one defined by filtered for this class
            agent_action = (filtered & eqs).forsome(mas.bddEnc.statesCube |
                                                    others_cube)
            compatible |= eqcl & agent_action
    return compatible
