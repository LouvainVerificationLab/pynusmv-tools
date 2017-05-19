"""
Utils functions.
"""

from pynusmv.dd import BDD
from pynusmv.utils import fixpoint

def agents_in_group(mas, group):
    """
    Return the list of agents in the given group in mas. If group is not a
    group of mas, group is returned alone.
    
    This procedure recursively searches for all basic agents in the groups
    possibly composing group.
    
    mas -- a multi-agent system;
    group -- a group or agent name of mas.
    """
    if group in mas.groups:
        agents = []
        for agent in mas.groups[group]:
            if agent in mas.groups:
                agents += [a for a in agents_in_group(mas, agent)
                           if a not in agents]
            else:
                agents.append(agent)
    else:
        agents = [group]
    return agents


def agents_in_list(mas, agents):
    """
    Return the list of agents in the given list of groups and agents.
    
    mas -- a multi-agent system;
    agents -- an iterable of groups and agents.
    """
    result = []
    for agent in agents:
        result += [a for a in agents_in_group(mas, agent)
                   if a not in result]
    return result


def Eequiv(mas, agents, states):
    """
    Return the set of states of mas that are equivalent to some state in states
    w.r.t. group knowledge of agents.
    
    mas -- a multi-agent system;
    agents -- a set of agents;
    states -- a subset of states of mas.
    """
    result = BDD.false(mas)
    for agent in agents_in_list(mas, agents):
        result |= mas.equivalent_states(states, {agent}) & mas.reachable_states
    return result
    

def Dequiv(mas, agents, states):
    """
    Return the set of states of mas that are equivalent to some state in states
    w.r.t. distributed knowledge of agents.
    
    mas -- a multi-agent system;
    agents -- a set of agents;
    states -- a subset of states of mas.
    """
    return mas.equivalent_states(states, {agents}) & mas.reachable_states
    

def Cequiv(mas, agents, states):
    """
    Return the set of states of mas that are equivalent to some state in states
    w.r.t. common knowledge of agents.
    
    mas -- a multi-agent system;
    agents -- a set of agents;
    states -- a subset of states of mas.
    """
    return fixpoint(lambda Z: Eequiv(mas, agents, states | Z),
                    BDD.false(fsm.bddEnc.DDmanager))

def reach(mas, states):
    """
    Return the set of states reachable from states in mas.
    
    mas -- a multi-agents system;
    states -- a subset of states of mas.
    """
    return fixpoint(lambda Z: states | mas.post(Z), BDD.false(mas))


def var_to_name(variable):
    """
    Given a variable of a model, return a name that can be used as an
    atom for the variable name.
    """
    return (str(variable).replace(".", "$").replace("[", "$").
            replace("]", "$"))

def assign_to_name(assigment):
    """
    Given an assigment of variables (an enumerable of var, val pairs),
    return a string that can be used as an atom for representing the
    assigment.
    """
    return "##".join(var_to_name(var) + "#" + val
                     for var, val in sorted(((str(var), str(val))
                                             for var, val in assigment)))


# ----- debugging -------------------------------------------------------------

def moves_to_dot(mas, agents, moves):
    """
    Return a dot encoding of the given mas with highlighted moves of agents.
    """
    
    init = mas.init & mas.state_constraints & mas.bddEnc.statesMask
    states = mas.pick_all_states(mas.reachable_states)
    transitions = {(s1,i,s2)
                   for s1 in states
                   for s2 in 
                   mas.pick_all_states(mas.post(s1) & mas.reachable_states)
                   for i in (mas.pick_all_inputs(
                                         mas.get_inputs_between_states(s1,s2))
                             if len(mas.bddEnc.inputsVars) > 0
                             else {None})
                   if s2 <= mas.post(s1, inputs=i)}
    
    dot = ["digraph {"]
    
    # Add states
    # Generate ids
    ids = dict()
    curid = 1
    for state in states:
        ids[state] = "s" + str(curid)
        curid = curid + 1
    
    # Print states
    for state in states:
        attr = {}
        # Label
        attr["label"] = '\\n'.join(var+"="+val for var, val
                                   in sorted(state.get_str_values().items()))
        # Initial state
        if state <= mas.init:
            attr["penwidth"] = 5
        # moves
        if state <= moves.forsome(mas.bddEnc.inputsCube):
            attr["color"] = "red"
        dot.append(ids[state] +
                   " [" +
                   ", ".join(key + "=\"" + str(value) + "\""
                             for key, value in attr.items()) +
                   "]")
      
        
    # Add transitions
    for s1, i, s2 in transitions:
        attr = {}
        # Label
        attr["label"] = '\\n'.join(var+"="+val for var, val
                                   in sorted(i.get_str_values().items()))
        # moves
        if s1 & i <= moves:
            attr["color"] = "red"
        dot.append(ids[s1] + " -> " + ids[s2] +
                   " [" +
                   ", ".join(key + "=\"" + str(value) + "\""
                             for key, value in attr.items()) +
                   "]")
    
    dot.append("}")
    
    return "\n".join(dot)
