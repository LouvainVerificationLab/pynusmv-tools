from .naive import evalATLK as eval_naive
from .partial import evalATLK as eval_partial
from .early import evalATLK as eval_early
from .symbolic import evalATLK as eval_symbolic
from .backward import evalATLK as eval_backward

__implementations = {"naive": eval_naive,
                     "partial": eval_partial,
                     "early": eval_early,
                     "symbolic": eval_symbolic,
                     "backward": eval_backward}

def check(mas, formula, implementation="naive", pre_filtering=False):
    """
    Return whether the system satisfies the ATLK formula.
    
    mas -- a multi-agents system;
    formula -- the specification, as a string;
    implem -- the particular implementation to use for strategic operators
              evaluation:
              * "naive" the naive implementation;
              * "partial" a version based on partial strategies;
              * "early" a version based on early evaluated partial strategies;
              * "symbolic" a version based on a fully symbolic approach.
    """
    if implementation in __implementations:
        sat = __implementations[implementation](mas,
                                                formula,
                                                pre_filtering=pre_filtering)
    else:
        raise Exception("check: unknown implementation: " + implementation)
    return (~sat & mas.bddEnc.statesInputsMask & mas.init).is_false()
