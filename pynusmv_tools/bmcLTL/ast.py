"""
This module contains the class definition of the different classes that may
compose an LTL abstract syntax tree.

.. note::
    The generation of the boolean expressions corresponding to the different
    LTL expressions could have been done using directly the functionalities
    provided :mod:`pynusmv.bmc.ltlspec`. However, the objective of the tool
    implemented in :mod:`pynusmv_tools.bmcLTL` is to demonstrate with a simple example
    (LTL) how one can use the bmc additions to PyNuSMV to develop verification
    tools for new logic formalisms. Hence, the approach that was adopted in that
    context was to *NOT* use any of the "higher level services" and develop
    a verification tool translating "literally" the reduction of that logic to
    a propositional SAT problem as imagined or stated in a reference paper.

    In this scope, the reference paper that was used was:

                Biere et al - ``Bounded Model Checking'' - 2003
"""
from pynusmv.bmc.glob      import master_be_fsm
from pynusmv.be.expression import Be
from pynusmv.wff           import Wff
from pynusmv.parser import parse_simple_expression

###############################################################################
# Memoization Utility functions:
###############################################################################
# The global cache of memoized values
MEMOIZER = {}

# creates a key for a cache entry
def MEMOIZER_key(fml, i, k, l):
    """
    Creates a key for a cache entry.
    
    :param fml: the formula object (typically 'self').
    :param i: the time index.
    :param k: the problem bound.
    :param l: the loop position. Set this value to -1 in the stright path case.
    :return: a key for the memoized entry _l[[fml]]^i_k
    """
    return (fml, i, k, l)

def MEMOIZER_get(key):
    """
    Retrieves a memoized entry by its key.
    
    :param key: the key (created with MEMOIZER_key) of the value to retrieve
    :return: the memoized value corresponding to key or none if nothing was found
    """
    return MEMOIZER.get(key)

def MEMOIZE_put(key, value):
    """
    Memoises `value` and associates it with `key`.
    
    :param key: the key (created with MEMOIZER_key) of the value to store
    :param value: the value to store
    """
    MEMOIZER[key] = value

def memoize_with_loop(fun):
    """
    The decorator to be applied on semantic_with_loop functions to activate the
    memoisation (makes the reduction to SAT linear).
    
    :param fun: the decorated function. (should be of the form:
        fun(fml, enc, i, k, l)
    """
    def memoized(fml, enc, i, k, l):
        key = MEMOIZER_key(fml, i, k, l)
        res = MEMOIZER_get(key)
        if res is None:
            res = fun(fml, enc, i, k, l)
            MEMOIZE_put(key, res)
        return res
    return memoized

def memoize_no_loop(fun):
    """
    The decorator to be applied on semantic_no_loop functions to activate the
    memoisation (makes the reduction to SAT linear).
    
    :param fun: the decorated function. (should be of the form:
        fun(fml, enc, i, k)
    """
    def memoized(fml, enc, i, k):
        key = MEMOIZER_key(fml, i, k, -1)
        res = MEMOIZER_get(key)
        if res is None:
            res = fun(fml, enc, i, k)
            MEMOIZE_put(key, res)
        return res
    return memoized   

###############################################################################
# LTL Utility functions:
###############################################################################
def successor(i, k, l):
    """
    Computes the successor of time `i` in a k-l loop.

    .. note::
        References, see Definition 6
        in Biere et al - ``Bounded Model Checking'' - 2003

    .. note::
        An other implementation of this function (w/ the same semantics) exists
        in :mod:`pynusmv.bmc.utils`. This version is merely re-implemented to
        1. show that it can be easily done
        2. stick closely to the definition given in the paper by Biere et al.
            (see other note)

    .. warning::
        To be consistent with the way the loop condition is implemented (equiv
        of all the state variables), we have that walking 'k' steps means to be
        back at step 'l'. Hence, the value of i can only vary from 0 to k-1
        (and will repeat itself in the range [l; k-1]

    :param i: the current time
    :param k: the maximum (horizon/bound) time of the problem
    :param l: the time where the loop starts

    :return: the k-l loop successor of i
    """
    return i+1 if i < k-1 else l

def loop_condition(enc, k, l):
    """
    This function generates a Be expression representing the loop condition
    which is necessary to determine that k->l is a backloop.

    Formally, the returned constraint is denoted _{l}L_{k}

    Because the transition relation is encoded in Nusmv as formula (and not as
    a relation per-se), we determine the existence of a backloop between
    l < k and forall var, var(i) == var(k)

    That is to say: if it is possible to encounter two times the same state
    (same state being all variables have the same value in both states) we know
    there is a backloop on the path

    .. note::
        An other implementation of this function (w/ the same semantics) exists
        in :mod:`pynusmv.bmc.utils`. This version is merely re-implemented to
        1. show that it can be easily done
        2. stick closely to the definition given in the paper by Biere et al.
            (see other note)


    :param fsm: the fsm on which the condition will be evaluated
    :param k: the highest time
    :param l: the time where the loop is assumed to start
    :return: a Be expression representing the loop condition that verifies that
        k-l is a loop path.
    """
    cond = Be.true(enc.manager)
    for v in enc.curr_variables: # for all untimed variable
        vl   = v.at_time[l].boolean_expression
        vk   = v.at_time[k].boolean_expression
        cond = cond & ( vl.iff(vk) )
    return cond

def fairness_constraint(fsm, k, l):
    """
    Computes a step of the constraint to be added to the loop side of the BE
    when one wants to take fairness into account for the case where we consider
    the existence of a k-l loop (between k and l obviously).

    :param fsm: the fsm whose transition relation must be unrolled
    :param k: the maximum (horizon/bound) time of the problem
    :param l: the time where the loop starts
    :return: a step of the fairness constraint to force fair execution on the
        k-l loop.
    """
    constraint = Be.true(fsm.encoding.manager)
    # nothing to generate, stop
    if k == 0:
        return constraint

    for fairness in fsm.fairness_iterator():
        # just a shortcut for the loop to create
        #    \bigvee_{l}^{k-1} (fairness_{l})
        constraint &= fsm.encoding.or_interval(fairness, l, k-1)
    return constraint

###############################################################################
# Abstract ast nodes
###############################################################################
class Formula:
    """An abstract base class meant to be the parent of all the AST nodes"""

    def bounded_semantics(self, fsm, k, fairness=True):
        """
        Returns a boolean expression corresponding to the bounded semantics of
        the formula denoted by `self` on a path of length k. This combines both
        the semantics in case of a loopy path and the case of a non-loopy path.

        .. note::
            This function takes the same approach as NuSMV and does not enforce
            the absence of loop when using the more restrictive semantic_no_loop.

        :param fsm: the FSM representing the model. It is used to gain access
            to the encoder (-> shift variables) and to obtain the list of
            fairness constraints.
        :param k: the last time that exists in the universe of this expression
        :param fairness: a flag indicating whether or not the fairness constraints
            should be taken into account while generating the formula.
        :return: a boolean expression translating the bounded semantics of this
            formula.
        """
        enc    = fsm.encoding
        noloop = self.semantic_no_loop(enc, 0, k)

        w_loop = Be.false(enc.manager)
        for l in range(k):   # [0; k-1]
            fairness_cond = fairness_constraint(fsm, k, l) \
                                 if fairness \
                                 else Be.true(enc.manager)

            w_loop |= (loop_condition(enc, k, l) \
                      & fairness_cond \
                      & self.semantic_with_loop(enc, 0, k, l))

        return noloop | w_loop

    def semantic_no_loop(self, enc, i, k):
        """
        All nodes of the AST must implement this function.
        Concretely, the role of this function is to generate a propositional
        equivalent to the bounded LTL semantic of this node when there is no
        loop on the path from state(time) to state(bound)

        ..math::
            [[self]]_{k}^{i}

        :param enc: the encoding used to store and organize the variables (used
            ie to shift vars)
        :param i: the time at which the generated expression will be considered
        :param k: the last time that exists in the universe of this expression
        :return: a boolean expression conform to the ltl bounded semantics of
            this node when there is no loop on the path from i to k
        """
        pass

    def semantic_with_loop(self, enc, i, k, l):
        """
        All nodes of the AST must implement this function.
        Concretely, the role of this function is to generate a propositional
        equivalent to the bounded LTL semantic of this node when there is no
        loop on the path from state(time) to state(bound)

        ..math::
            _{l}[[self]]_{k}^{i}

        .. note::
            There are essentially two cases for the loop:

                1. i < l         (not yet entered in the loop)
                2. l <= i < k    (inside the loop)

            Therefore, l is allowed to range from 0 to k. However, you don't
            need to deal with all the positions for yourself: the propblem
            generation method is responsible to call you with all the possible
            values of `l`. You may however compare l and k to test if you have
            reached the horizon of your bounded problem generation.

        :param enc: the encoding used to store and organize the variables (used
            ie to shift vars)
        :param i: the time at which the generated expression will be considered
        :param k: the last time that exists in the universe of this expression
        :param l: l is the time position where the loop starts.
        :return: a boolean expression conform to the ltl bounded semantics of
            this node when there is no loop on the path from i to k
        """
        pass

    def nnf(self, negated):
        """
        All nodes of the AST must implement this function.
        Concretely, the role of this function is to return a version of `self`
        that is formatted according to the Negative Normal Form.

        :param negated: a flag indicating whether or not the subformula
            represented by self was negated in the parent formula
        :return: a nnf version of self
        """
        pass

class Atomic(Formula):
    """An abstract base class representing AST of an atomic proposition"""
    def __init__(self, x):
        self.id = x

    def __repr__(self):
        return "{}({})".format(type(self).__name__, self.id)

class Unary(Formula):
    """An abstract base class representing AST of an unary proposition"""
    def __init__(self, prop):
        self.prop = prop

    def __repr__(self):
        return "({} {})".format(type(self).__name__, self.prop)

class Binary(Formula):
    """An abstract base class representing AST of a binary proposition"""
    def __init__(self, lhs=None, rhs=None):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return "({} {} {})".format(self.lhs, type(self).__name__, self.rhs)

###############################################################################
# Propositional logic ast nodes
###############################################################################
class Constant(Atomic):
    def semantic_no_loop(self, enc, i, k):
        if self.id == "TRUE":
            return Be.true(enc.manager)
        else:
            return Be.false(enc.manager)

    def semantic_with_loop(self, enc, i, k, l):
        return self.semantic_no_loop(enc, i, k)

    def nnf(self, negated):
        if not negated:
            return self
        else:
            return Constant("FALSE") if self.id == "TRUE" else Constant("TRUE")

class Proposition(Atomic):
    def __init__(self, x):
        super().__init__(x)
        self._booleanized = None
        
    def _booleanize(self):
        """
        Returns a boolean expression (Be) corresponding to this simple
        boolean expression (text).

        .. note::
            Albeit feasible, working directly with variables as offered by the
            encoding is a little bit limiting as it de facto rejects any symbol
            which is not a variable. As a consequence, the DEFINES, or
            arithmetic expressions are not usable.

            The use of this function palliates that limitation and makes the
            use of any simple boolean expression possible.

        :return: a be expression (Be) corresponding to `self`
        """
        if not self._booleanized:
            befsm = master_be_fsm()
            node  = parse_simple_expression(self.id)
            self._booleanized = Wff(node).to_boolean_wff().to_be(befsm.encoding)
        return self._booleanized

    def _at_time(self, time):
        """
        Returns a boolean expression (Be) corresponding to this simple
        boolean expression (text) at the time step `time`.

        .. note::
            Albeit feasible, working directly with variables as offered by the
            encoding is a little bit limiting as it de facto rejects any symbol
            which is not a variable. As a consequence, the DEFINES, or
            arithmetic expressions are not usable.

            The use of this function palliates that limitation and makes the
            use of any simple boolean expression possible.

        :param time: the time at which the symbol should be shifted.
        :return: a be expression (Be) corresponding to `self` at `time`
        """
        booleanized = self._booleanize()
        return master_be_fsm().encoding.shift_to_time(booleanized, time)

    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        return self._at_time(i)

    def semantic_with_loop(self, enc, i, k, l):
        return self.semantic_no_loop(enc, i, k)

    def nnf(self, negated):
        return self if not negated else Not(self)

class Not(Unary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        return - self.prop.semantic_no_loop(enc, i, k)

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        return -self.prop.semantic_with_loop(enc, i, k, l)

    def nnf(self, negated):
        # double negation removes itself altogether
        return self.prop.nnf(True) if not negated else self.prop.nnf(False)

class And(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        lhs = self.lhs.semantic_no_loop(enc, i, k)
        rhs = self.rhs.semantic_no_loop(enc, i, k)
        return lhs & rhs

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        lhs = self.lhs.semantic_with_loop(enc, i, k, l)
        rhs = self.rhs.semantic_with_loop(enc, i, k, l)
        return lhs & rhs

    def nnf(self, negated):
        if not negated:
            return And(self.lhs.nnf(False), self.rhs.nnf(False))
        else:
            return Or(self.lhs.nnf(True), self.rhs.nnf(True))


class Or(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        lhs = self.lhs.semantic_no_loop(enc, i, k)
        rhs = self.rhs.semantic_no_loop(enc, i, k)
        return lhs | rhs

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        lhs = self.lhs.semantic_with_loop(enc, i, k, l)
        rhs = self.rhs.semantic_with_loop(enc, i, k, l)
        return lhs | rhs

    def nnf(self, negated):
        if not negated:
            return Or(self.lhs.nnf(False), self.rhs.nnf(False))
        else:
            return And(self.lhs.nnf(True), self.rhs.nnf(True))

class Xor(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        lhs = self.lhs.semantic_no_loop(enc, i, k)
        rhs = self.rhs.semantic_no_loop(enc, i, k)
        return lhs ^ rhs

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        lhs = self.lhs.semantic_with_loop(enc, i, k, l)
        rhs = self.rhs.semantic_with_loop(enc, i, k, l)
        return lhs ^ rhs

    def nnf(self, negated):
        if not negated:
            return Xor(self.lhs.nnf(False), self.rhs.nnf(False))
        else:
            # rewrite using : p ^ q <=> (p | q) & !(p & q)
            rewrite = And(Or(self.lhs, self.rhs), Not(And(self.lhs, self.rhs)))
            return rewrite.nnf(negated)

class Imply(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        lhs = self.lhs.semantic_no_loop(enc, i, k)
        rhs = self.rhs.semantic_no_loop(enc, i, k)
        return lhs.imply(rhs)

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        lhs = self.lhs.semantic_with_loop(enc, i, k, l)
        rhs = self.rhs.semantic_with_loop(enc, i, k, l)
        return lhs.imply(rhs)

    def nnf(self, negated):
        return Or(Not(self.lhs), self.rhs).nnf(negated)

class Equiv(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        lhs = self.lhs.semantic_no_loop(enc, i, k)
        rhs = self.rhs.semantic_no_loop(enc, i, k)
        return lhs.iff(rhs)

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        lhs = self.lhs.semantic_with_loop(enc, i, k, l)
        rhs = self.rhs.semantic_with_loop(enc, i, k, l)
        return lhs.iff(rhs)

    def nnf(self, negated):
        return And(Imply(self.lhs, self.rhs), Imply(self.rhs, self.lhs)).nnf(negated)

###############################################################################
# LTL specific ast nodes
###############################################################################

class Until(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        """The semantics when there is no loop:: [[lhs U rhs]]_{bound}^{time}"""
        # k is not infinity when there is no loop
        if i > k:
            return Be.false(enc.manager)

        psi = self.rhs.semantic_no_loop(enc, i, k)
        phi = self.lhs.semantic_no_loop(enc, i, k)
        return psi | (phi & self.semantic_no_loop(enc, i+1, k))

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        """The semantics when there is a loop:: _{l}[[lhs U rhs]]_{bound}^{time}"""
        # without moving at least one step, it is impossible to go through a loop
        if k == 0:
            return Be.false(enc.manager)

        def _semantic(time, cnt):
            """auxiliary function to stop recursing after k steps"""
            # at infinity, it is false: psi MUST happen at some time
            if cnt == k:
                return Be.false(enc.manager)
            psi = self.rhs.semantic_with_loop(enc, time, k, l)
            phi = self.lhs.semantic_with_loop(enc, time, k, l)
            return psi | (phi & _semantic(successor(time, k, l), cnt+1))

        return _semantic(i, 0)

    def nnf(self, negated):
        if not negated:
            return Until(self.lhs.nnf(False), self.rhs.nnf(False))
        else:
            # pseudo duality rule
            phi = self.lhs.nnf(True)
            psi = self.rhs.nnf(True)
            return WeakUntil(psi, And(phi, psi))

class WeakUntil(Binary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        """The semantics when there is no loop:: [[lhs W rhs]]_{bound}^{time}"""
        # k is not infinity when there is no loop
        if i > k:
            return Be.false(enc.manager)

        psi = self.rhs.semantic_no_loop(enc, i, k)
        phi = self.lhs.semantic_no_loop(enc, i, k)
        return psi | (phi & self.semantic_no_loop(enc, i+1, k))

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        """The semantics when there is a loop:: _{l}[[lhs W rhs]]_{bound}^{time}"""
        # without moving at least one step, it is impossible to go through a loop
        if k == 0:
            return Be.false(enc.manager)

        def _semantic(time, cnt):
            """auxiliary function to stop recursing after k steps"""
            # at infinity, it is true: psi is not forced if []phi
            if cnt == k:
                return Be.true(enc.manager)
            psi = self.rhs.semantic_with_loop(enc, time, k, l)
            phi = self.lhs.semantic_with_loop(enc, time, k, l)
            return psi | (phi & _semantic(successor(time, k, l), cnt+1))

        return _semantic(i, 0)

    def nnf(self, negated):
        if not negated:
            return WeakUntil(self.lhs.nnf(False), self.rhs.nnf(False))
        else:
            # pseudo duality rule
            phi = self.lhs.nnf(True)
            psi = self.rhs.nnf(True)
            return Until(psi, And(phi, psi))

class Globally(Unary):
    def semantic_no_loop(self, enc, i, k):
        return Be.false(enc.manager)
    
    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        # without moving at least one step, it is impossible to go through a loop
        if k == 0:
            return Be.false(enc.manager)

        def _semantic(time, cnt):
            if cnt == k:
                return Be.true(enc.manager)
            now = self.prop.semantic_with_loop(enc, time, k, l)
            return now & _semantic(successor(time, k, l), cnt+1)

        return _semantic(i, 0)

    def nnf(self, negated):
        if not negated:
            return Globally(self.prop.nnf(False))
        else:
            return Eventually(self.prop.nnf(True))

class Eventually(Unary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        if i > k:
            return Be.false(enc.manager)
        
        now = self.prop.semantic_no_loop(enc, i, k)
        return now | self.semantic_no_loop(enc, i+1, k)

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        # without moving at least one step, it is impossible to go through a loop
        if k == 0:
            return Be.false(enc.manager)
        
        def _semantic(time, cnt):
            if cnt == k:
                return Be.false(enc.manager)
            now = self.prop.semantic_with_loop(enc, time, k, l)
            return now | _semantic(successor(time, k, l), cnt+1)
        
        return _semantic(i, 0)

    def nnf(self, negated):
        if not negated:
            return Eventually(self.prop.nnf(False))
        else:
            return Globally(self.prop.nnf(True))

class Next(Unary):
    @memoize_no_loop
    def semantic_no_loop(self, enc, i, k):
        if i >= k:
            return Be.false(enc.manager)
        else:
            return self.prop.semantic_no_loop(enc, i+1, k)

    @memoize_with_loop
    def semantic_with_loop(self, enc, i, k, l):
        # without moving at least one step, it is impossible to go through a loop
        if k == 0:
            return Be.false(enc.manager)

        return self.prop.semantic_with_loop(enc, successor(i, k, l), k, l)

    def nnf(self, negated):
        return Next(self.prop.nnf(negated))
        
