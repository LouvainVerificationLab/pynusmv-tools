from pynusmv.be.expression import Be 

def model_problem(fsm, bound):
    """
    Computes the unrolled transition relation [[M]]_{k}
    
    .. note:: 
        this is equivalent to :see:`pynusmv.bmc.utils.BmcModel.path(bound)`
    
    :param fsm: the fsm whose transition relation must be unrolled
    :param bound: the bound up to which the transition relation must be unrolled
    :return: the unrolled transition relation of `fsm`
    """
    enc   = fsm.encoding
    # initial state
    init0 = enc.shift_to_time(fsm.init, 0)
    # transition relation (unrolled k steps)
    trans = Be.true(enc.manager)
    for k in range(bound):
        trans = trans & enc.shift_to_time(fsm.trans, k)
    
    return init0 & trans

def invariants_constraint(fsm, k):
    """
    Computes the constraint to be added to the model when one wants to 
    enforce the invariants declared in the SMV text.
    
    .. note:: 
        This constraint has no counterpart in BmcModel. However, the same
        result can be achieved by computing the conjunction of 
        BmcModel.invar[time] for all the times in the range [0; k]. 
    
    :param fsm: the fsm whose transition relation must be unrolled
    :param k: the maximum (horizon/bound) time of the problem
    :return: the invariants constraint enforced on the paths.
    """
    # I know, thisone is REALLY easy!
    # note: the and_interval is just a shortcut for
    #    \bigwedge_{i=0}^{k} (invariants_{i})
    return fsm.encoding.and_interval(fsm.invariants, 0, k)

def generate_problem(fml, fsm, k=10, no_fairness=False, no_invar=False):
    """
    Generates a formula representing a SAT problem that is satisfiable iff
    the the `fsm` violates the formula represented in `formula_text`.
    
    Mathematically, this function computes the following formula:
    .. math:: [[M, f]]_{k}
    
    :param fml: an LTL formula parsed with `pynusmv_tools.bmcLTL.parsing` (hence the 
        abstract syntax tree of that formula). Note, this is *NOT* the NuSMV
        format (Node).
    :param fsm: the FSM representing the model.
    :param k: the maximum (horizon/bound) time of the problem
    :param no_fairness: a flag telling whether or not the generated problem should
        focus on fair executions only (the considered fairness constraints must
        be declared in the SMV model).
    :param no_invar: a flag telling whether or not the generated problem 
        should enforce the declared invariants (these must be declared in the
        SMV text).
    :return: a Be expression that is satisfiable iff the fsm can violate the 
        stated property [[M, f]]_{k}
    """
    negated = fml.nnf(True)
    
    problem = model_problem(fsm, k) & \
              negated.bounded_semantics(fsm, k, fairness = not no_fairness)
    
    # enforce invariants if needed
    if not no_invar:
        problem &= invariants_constraint(fsm, k)
        
    return problem