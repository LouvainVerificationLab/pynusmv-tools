"""
Functions to compute mu-calculus models with NuSMV.
"""

from pynusmv_lower_interface.nusmv.compile.symb_table import symb_table as nssymb_table
from pynusmv_lower_interface.nusmv.compile import compile as nscompile
from pynusmv_lower_interface.nusmv.node import node as nsnode

from pynusmv.exception import NuSMVNoReadModelError
from pynusmv.parser import parse_simple_expression, parse_next_expression

from pynusmv.glob import (load_from_file, load_from_string,
                          load_from_modules, load,
                          flatten_hierarchy as _flatten_hierarchy,
                          symb_table, bdd_encoding,
                          prop_database as _prop_database,
                          compute_model as _compute_model)
from pynusmv.mc import eval_simple_expression
from pynusmv.fsm import BddFsm, BddTrans

from . import MuCalculusError, MuCalculusModelError, UnknownTransitionError

import itertools


class InputsBasedBddTrans(BddTrans):
    """
    A BDD-encoded transition relation based on a classical BDD-encoded
    transition relation and a given inputs. Every transition evaluation is
    restricted by this inputs.
    
    The idea behind this inputs is to be able to define different transition
    relations based on the same definition but with additional restrictions.
    """
    
    def __init__(self, ptr, inputs, enc=None, manager=None, freeit=True):
        """
        Create a new InputsBasedBddTrans.

        :param ptr: a NuSMV pointer to a BddTrans
        :param inputs: a BDD representing the inputs retricting this transition
                       relation
        :param enc: the BDD encoding of the transition relation
        :type enc: :class:`BddEnc`
        :param manager: the DD manager of the BDDs used to encode the relation
        :type manager: :class:`DDManager <pynusmv.dd.DDManager>`
        :param freeit: whether or not freeing the pointer

        """
        super(InputsBasedBddTrans, self).__init__(ptr, enc=enc,
                                                  manager=manager,
                                                  freeit=freeit)
        self._inputs = inputs
    
    def pre(self, states, inputs=None):
        """
        Compute the pre-image of `states`, through `inputs` if not `None`.

        :param states: the concerned states
        :type states: :class:`BDD <pynusmv.dd.BDD>`
        :param inputs: possible inputs
        :type inputs: :class:`BDD <pynusmv.dd.BDD>`
        :rtype: :class:`BDD <pynusmv.dd.BDD>`

        """
        inputs = self._inputs & inputs if inputs else self._inputs
        return super(InputsBasedBddTrans, self).pre(states, inputs=inputs)

    def post(self, states, inputs=None):
        """
        Compute the post-image of `states`, through `inputs` if not `None`.

        :param states: the concerned states
        :type states: :class:`BDD <pynusmv.dd.BDD>`
        :param inputs: possible inputs
        :type inputs: :class:`BDD <pynusmv.dd.BDD>`
        :rtype: :class:`BDD <pynusmv.dd.BDD>`

        """
        inputs = self._inputs & inputs if inputs else self._inputs
        return super(InputsBasedBddTrans, self).post(states, inputs=inputs)
    
    @classmethod
    def from_trans(cls, symb_table, inputs, trans, context=None):
        """
        Return a new ReversedBddTrans from the given trans.

        :param symb_table: the symbols table used to flatten the trans
        :type symb_table: :class:`SymbTable`
        :param trans: the parsed string of the trans, not flattened
        :param inputs: the inputs to restrict this transition relation
        :param context: an additional parsed context, in which trans will be
                        flattened, if not None
        :rtype: :class:`BddTrans`
        :raise: a :exc:`NuSMVFlatteningError
                <pynusmv.exception.NuSMVFlatteningError>`
                if `trans` cannot be flattened under `context`

        """
        original = BddTrans.from_trans(symb_table, trans, context)
        return InputsBasedBddTrans(original._ptr, inputs,
                                   original._enc, original._manager,
                                   freeit=True)


class BddMuModel(BddFsm):
    """
    The BDD representation of a mu-calculus model.
    
    A mu-calculus model is an FSM with sereval transition relations.
    """
    
    def __init__(self, ptr, transitions, freeit=False):
        """
        Create a new mu-calculus model.
        
        ptr -- the pointer of the NuSMV FSM
        transitions -- a dictionary of transition names -> BddTrans.
        freeit -- whether or not free the pointer
        """
        super(BddMuModel, self).__init__(ptr, freeit = freeit)
        self.transitions = transitions
    
    
    def pre(self, states, transition="time", inputs=None):
        """
        Return the pre-image of states in this model through transition.
        
        If inputs is not None, it is used to restrict the pre-image
        computation.
        
        states -- the BDD representing the set of states;
        transition -- the transition name;
        inputs -- if not None, a BDD on inputs variables, restricting the
                  pre-image.
        
        """
        if transition not in self.transitions:
            raise UnknownTransitionError("Unknown transition " +
                                         str(transition))
        return self.transitions[transition].pre(states, inputs=inputs)
    
    
    def post(self, states, transition="time", inputs=None):
        """
        Return the post-image of states in this model through transition.
        
        If inputs is not None, it is used to restrict the post-image
        computation.
        
        states -- the BDD representing the set of states;
        transition -- the transition name;
        inputs -- if not None, a BDD on inputs variables, restricting the
                  post-image.
        
        """
        if transition not in self.transitions:
            raise UnknownTransitionError("Unknown transition " + transition)
        return self.transitions[transition].post(states, inputs=inputs)


# The current model
__bddmodel = None

def reset_globals():
    """
    Reset mucalculus.model related global variables.
    
    Must be called whenever (and before) pynusmv.init.init.deinit_nusmv
    is called.
    
    """
    global __bddmodel
    __bddmodel = None


def bddModel(transitions=None, variables_ordering=None):
    """
    Return (and compute if needed) the model represented by the currently read
    SMV model.
    
    transitions -- if not None, a dictionary of transition relation names ->
                   transition relations expressions as strings.
    variables_ordering -- if not None, a path to a variables order file.
    
    The currently read SMV model must be defined in terms of an input variable
    named 'transition' with an enum type. All the possible values of this
    'transition' input variable are considered as different transition
    relations and the returned BddModel is based on them.
    
    If such a transition input variable is not defined, the standard transition
    relation of the model is used and named "time".
    
    If transitions is not None, additional transition relations a built and
    added to the return BddModel.
    
    """    
    global __bddmodel
    if __bddmodel is None:
        # Check cmps
        if not nscompile.cmp_struct_get_read_model(nscompile.cvar.cmps):
            raise NuSMVNoReadModelError("Cannot build model; no read file.")        
        # Compute the model
        _compute_model(variables_ordering=variables_ordering)
        
        # Check that transition exists and is an input variable enum
        # Get transition node
        transition = parse_simple_expression("transition")
        st = symb_table()
        
        # Resolve name and get category
        rs = nssymb_table.SymbTable_resolve_symbol(st._ptr, transition, None)
        tr_name = nssymb_table.ResolveSymbol_get_resolved_name(rs)
        if not nssymb_table.ResolveSymbol_is_defined(rs):
            # Transition is missing
            # Create the model
            fsm = _prop_database().master.bddFsm
            # Create embedded transition relations
            relations = {"time": fsm.trans}
        else:
            tr_category = nssymb_table.SymbTable_get_symbol_category(st._ptr,
                                                                     tr_name)
            
            # If constant, check that is a define and get value
            if tr_category == nssymb_table.SYMBOL_CONSTANT:
                # Check transition is a define
                if not nssymb_table.SymbTable_is_symbol_define(st._ptr,
                                                               tr_name):
                    raise MuCalculusModelError("Transition should be an input "
                                               "variable.")
                tr_value = (nssymb_table.
                            SymbTable_get_define_flatten_body(st._ptr,
                                                              tr_name))
                tr_names = {nsnode.sprint_node(tr_value)}
                
            # If input var, check that is an enum
            elif tr_category == nssymb_table.SYMBOL_INPUT_VAR:
                tr_type = nssymb_table.SymbTable_get_var_type(st._ptr, tr_name)
                if not nssymb_table.SymbType_is_enum(tr_type):
                    raise MuCalculusModelError("Transition should be an enum "
                                               "type.")
                tr_values = nssymb_table.SymbType_get_enum_type_values(tr_type)
                tr_names = set()
                while tr_values is not None:
                    tr_value = nsnode.car(tr_values)
                    tr_names.add(nsnode.sprint_node(tr_value))
                    tr_values = nsnode.cdr(tr_values)
            else:
                raise MuCalculusModelError("Transition should be an input "
                                           "variable.")
            
            # Create the model
            fsm = _prop_database().master.bddFsm
            
            # Create embedded transition relations
            relations = {}
            original_trans = fsm.trans
            enc = original_trans._enc
            manager = original_trans._manager
            for tr_name in tr_names:
                inputs = eval_simple_expression(fsm, 'transition =' + tr_name)
                relations[tr_name] = InputsBasedBddTrans(original_trans._ptr,
                                                         inputs, enc=enc,
                                                         manager=manager,
                                                         freeit=False)
        
        # Create additional transition relations
        if transitions is not None:
            for tr_name, tr_expr in transitions.items():
                relations[tr_name] = BddTrans.from_string(st, tr_expr)
        
        __bddmodel = BddMuModel(fsm._ptr, relations, freeit=False)
        
    return __bddmodel